module StrMap = Map.Make (String)

type tkmap = (Type.t * Type.t) StrMap.t

type tctx = {
  id : Int64.t;
  tctors : tkmap;
  dctors : Type.t StrMap.t;
  tvenv : tkmap list;
  idenv : Type.t StrMap.t list;
  rules : (Type.t * Type.t) list;
  subst : Type.t VarInfo.Map.t;
}

let map_of_list (list : (string * 'a) list) =
  list |> List.to_seq |> StrMap.of_seq

let core_tctx : tctx = {
  id = 0L;

  tctors = map_of_list ([
    "(->)", (TCons (TCtorArr, []), TArr (TKind, TArr (TKind, TKind)));
    "[]", (TCons (TCtorVar Type.varList, []), TArr (TKind, TKind));
    "Char", (TChr, TKind);
    "String", (TStr, TKind);
    "Int", (TInt, TKind);
    "Bool", (Type.tyBool, TKind);
  ] : (string * (Type.t * Type.t)) list);
  dctors = map_of_list (
    Type.quantize_cases Type.varList @
    Type.quantize_cases Type.varBool);

  idenv = [];
  tvenv = [];
  rules = [];
  subst = VarInfo.Map.empty;
}

let lookup_env (name : string) (env : 'a StrMap.t list) =
  let rec loop = function
    | [] -> None
    | x :: xs ->
      match StrMap.find_opt name x with
        | None -> loop xs
        | Some v -> Some v in
  loop env

let instantiate (tctx : tctx) (t : Type.t) =
  let rec loop tctx acc map = function
    | Type.TQuant (q, t) ->
      let fresh = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      loop tctx (fresh :: acc) (VarInfo.Map.add q fresh map) t
    | t ->
      let t =
        if VarInfo.Map.is_empty map then t
        else Type.eval map VarInfo.Set.empty t in
      (t, List.rev acc, tctx) in
  loop tctx [] VarInfo.Map.empty t

let merge_errors (results : ('a, 'b list) result list) : 'b list =
  let rec loop acc = function
    | [] -> List.rev acc
    | [Error lst] -> List.rev_append acc lst
    | Error lst :: xs -> loop (List.rev_append lst acc) xs
    | _ :: xs -> loop acc xs in
  loop [] results

let visit_ast_type (allow_ign : bool) (next : tkmap option) (tctx : tctx) (ast : Ast.ast_typ) =
  let rec visit next tctx = function
    | Ast.TypeIgn ->
      if allow_ign then
        let ty = Type.TVar ("_", tctx.id)
        and kind = Type.TVar ("", tctx.id)
        and tctx = { tctx with id = Int64.succ tctx.id } in
        (Ok (ty, kind), next, tctx)
      else (Error ["unnamed type not allowed in this context"], next, tctx)
    | Ast.TypeVar n -> begin
      let tvenv = match next with
        | Some m -> m :: tctx.tvenv
        | None -> tctx.tvenv in
      match lookup_env n tvenv with
        | Some (ty, kind) -> (Ok (ty, kind), next, tctx)
        | None ->
          match next with
            | None -> (Error ["unknown type variable named " ^ n], next, tctx)
            | Some m ->
              let ty = Type.TVar (n, tctx.id)
              and kind = Type.TVar ("", tctx.id)
              and tctx = { tctx with id = Int64.succ tctx.id } in
              (Ok (ty, kind), Some (StrMap.add n (ty, kind) m), tctx)
    end
    | Ast.TypeCtor n -> begin
      match StrMap.find_opt n tctx.tctors with
        | None -> (Error ["unknown type constructor named " ^ n], next, tctx)
        | Some (ty, kind) ->
          let (kind, _, tctx) = instantiate tctx kind in
          (Ok (ty, kind), next, tctx)
    end
    | Ast.TypeApp (p, q) -> begin
      let (p, next, tctx) = visit next tctx p in
      let (q, next, tctx) = visit next tctx q in
      match (p, q) with
        | (Error p, Error q) -> (Error (p @ q), next, tctx)
        | (Error p, _) | (_, Error p) -> (Error p, next, tctx)
        | (Ok (p, pkind), Ok (q, qkind)) ->
          let kind = Type.TVar ("", tctx.id)
          and tctx = { tctx with id = Int64.succ tctx.id } in
          let rules = (pkind, Type.TArr (qkind, kind)) :: tctx.rules in
          (Ok (Type.TApp (p, q), kind), next, { tctx with rules })
    end
    | Ast.TypeTup xs -> begin
      let rec loop acc next tctx = function
        | [] ->
          let mapf xs = (Type.TTup (List.rev xs), Type.TKind) in
          (Result.map mapf acc, next, tctx)
        | x :: xs ->
          let (x, next, tctx) = visit next tctx x in
          match (acc, x) with
            | (Error p, Error q) -> loop (Error (p @ q)) next tctx xs
            | (Error p, _) | (_, Error p) -> loop (Error p) next tctx xs
            | (Ok acc, Ok (x, xkind)) ->
              let rules = (xkind, Type.TKind) :: tctx.rules in
              loop (Ok (x :: acc)) next { tctx with rules } xs in
      loop (Ok []) next tctx xs
    end in

  match visit next tctx ast with
    | (Ok (ty, kind), next, tctx) ->
      let ty = Type.normalize ty in
      if Type.contains_quant ty then
        (Error ["unsaturated type aliases are not allowed"], tctx)
      else (Ok (ty, kind, next), tctx)
    | (Error e, _, tctx) -> (Error e, tctx)

let visit_alias (tctx : tctx) (ast : Ast.ast_alias) =
  let (n, args, t) = ast in
  let rec tail tctx map acc errors = function
    | [] ->
      if errors = [] then begin
        let old_env = tctx.tvenv in
        let old_rules = tctx.rules in
        match visit_ast_type false None { tctx with tvenv = [map]; rules = [] } t with
          | (Error e, _) -> Error e
          | (Ok (t, k, _), tctx) ->
            let (subst, errors) = Type.unify VarInfo.Map.empty tctx.rules in
            match errors with
              | _ :: _ -> Error (List.map (Type.explain ~env:(Some subst)) errors)
              | [] ->
                let (k, subst) = Type.expand subst k in
                let foldf (t, k, subst) (q, qk) =
                  let (qk, subst) = Type.expand subst qk in
                  (Type.TQuant (q, t), Type.TArr (qk, k), subst) in
                let (t, k, _) = List.fold_left foldf (t, k, subst) acc in
                let (quants, k) = Type.gen VarInfo.Set.empty k in
                let k = List.fold_right (fun q k -> Type.TQuant (q, k)) quants k in
                Ok (n, t, k, { tctx with tvenv = old_env; rules = old_rules })
      end else Error (List.rev errors)
    | x :: xs ->
      let name = (x, 0L) in
      let kind = Type.TVar ("", tctx.id) in
      let tctx = { tctx with id = Int64.succ tctx.id } in
      let updatef = function
        | None -> Some (Type.TRigid name, kind)
        | t -> t in
      let next = StrMap.update x updatef map in
      if next == map then
        tail tctx next acc (("duplicate type variable " ^ x) :: errors) xs
      else
        tail tctx next ((name, kind) :: acc) errors xs in
  tail tctx StrMap.empty [] [] args

let merge_map m overwrite =
  StrMap.fold StrMap.add overwrite m

let gen_tuple_shape tctx elts =
  let rec loop acc tctx = function
    | [] -> (List.rev acc, tctx)
    | _ :: xs ->
      let ty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      loop (ty :: acc) tctx xs in
  loop [] tctx elts

let visit_pat (ty : Type.t) (next : tkmap) (tctx : tctx) (ast : Ast.ast_pat) =
  let rec visit captures next ty tctx = function
    | Ast.Cap None ->
      (Ok (Ast.Cap None, captures), next, tctx)
    | Ast.Cap (Some n) -> begin
      match StrMap.find_opt n captures with
        | Some _ -> (Error ["repeated capture of " ^ n], next, tctx)
        | None -> (Ok (Ast.Cap (Some n), StrMap.add n ty captures), next, tctx)
    end
    | Ast.Match (LitInt _) as t ->
      let rules = (ty, Type.TInt) :: tctx.rules in
      (Ok (t, captures), next, { tctx with rules })
    | Ast.Match (LitStr _) as t ->
      let rules = (ty, Type.TStr) :: tctx.rules in
      (Ok (t, captures), next, { tctx with rules })
    | Ast.Match (LitChar _) as t ->
      let rules = (ty, Type.TChr) :: tctx.rules in
      (Ok (t, captures), next, { tctx with rules })
    | Ast.Detup xs ->
      let (shape, tctx) = gen_tuple_shape tctx xs in
      let tctx = { tctx with rules = (ty, TTup shape) :: tctx.rules } in

      (* then trickle type information (if present) down to each element *)
      let rec loop acc captures next tctx = function
        | ([], []) -> (Ok (Ast.Detup (List.rev acc), captures), next, tctx)
        | (x :: xs, y :: ys) -> begin
          match visit captures next x tctx y with
            | (Ok (p, captures), next, tctx) ->
              loop (p :: acc) captures next tctx (xs, ys)
            | error -> error
        end
        | _ -> failwith "IMPOSSIBLE DIMENSION MISMATCH" in
      loop [] captures next tctx (shape, xs)
    | Ast.Delist xs ->
      let ety = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let tctx = { tctx with rules = (ty, Type.tyList ety) :: tctx.rules } in
      let rec loop acc captures next tctx = function
        | [] ->
          let p = Ast.Decons ("[]", []) in
          let p = List.fold_left (fun xs x -> Ast.Decons ("(::)", [x; xs])) p acc in
          (Ok (p, captures), next, tctx)
        | x :: xs ->
          match visit captures next ety tctx x with
            | (Ok (p, captures), next, tctx) ->
              loop (p :: acc) captures next tctx xs
            | error -> error in
      loop [] captures next tctx xs
    | Ast.Alternate (p, q) -> begin
      (* need to make sure both subpats capture the same things *)
      let (p, next, tctx) = visit StrMap.empty next ty tctx p in
      let (q, next, tctx) = visit StrMap.empty next ty tctx q in
      match (p, q) with
        | (Ok (p, pcap), Ok (q, qcap)) -> begin
          let rec loop pkv qcap captures tctx =
            match pkv () with
              | Seq.Nil -> begin
                match StrMap.choose_opt qcap with
                  | None -> (Ok (Ast.Alternate (p, q), captures), next, tctx)
                  | Some (cap, _) ->
                    (Error ["binding " ^ cap ^ " is only captured on one branch"], next, tctx)
              end
              | Seq.Cons ((cap, ty1), tl) ->
                match StrMap.find_opt cap qcap with
                  | None ->
                    (Error ["binding " ^ cap ^ " is only captured on one branch"], next, tctx)
                  | Some ty2 ->
                    match StrMap.find_opt cap captures with
                      | Some _ -> (Error ["repeated capture of " ^ cap], next, tctx)
                      | None ->
                        let rules = (ty1, ty2) :: tctx.rules in
                        loop tl
                          (StrMap.remove cap qcap)
                          (StrMap.add cap ty1 captures)
                          { tctx with rules } in
          loop (StrMap.to_seq pcap) qcap captures tctx
        end
        | _ -> (Error (merge_errors [p; q]), next, tctx)
    end
    | Ast.PatternTyped (p, annot) -> begin
      (* solve the type first to help resolve ambiguous data constructors *)
      let (annot, tctx) = visit_ast_type true (Some next) tctx annot in
      match annot with
        | Error p -> (Error p, next, tctx)
        | Ok (_, _, None) -> failwith "IMPOSSIBLE NO NEXT TVENV RETURNED"
        | Ok (annotty, kind, Some next) ->
          let rules = (kind, Type.TKind) :: (annotty, ty) :: tctx.rules in
          let (subst, errors) = Type.unify tctx.subst rules in
          let tctx = { tctx with subst; rules = [] } in
          match errors with
            | [] -> visit captures next ty tctx p
            | _ ->
              (Error (List.map (Type.explain ~env:(Some subst)) errors), next, tctx)
    end
    | _ -> (Error ["TODO"], next, tctx) in

  match visit StrMap.empty next ty tctx ast with
    | (Error e, _, tctx) -> (Error e, tctx)
    | (Ok (p, captures), next, tctx) -> (Ok (p, captures, next), tctx)

let visit_expr (ty : Type.t) (tctx : tctx) (ast : Ast.ast_expr) =
  let open Expr in
  let rec visit_cases sty ety tctx cases =
    let rec loop acc tctx = function
      | [] -> (Ok (List.rev acc), tctx)
      | (p, e) :: xs ->
        let (p, tctx) = visit_pat sty StrMap.empty tctx p in
        match p with
          | Error e -> (Error e, tctx)
          | Ok (p, new_ids, new_tvs) ->
            let tctx = { tctx with
              idenv = new_ids :: tctx.idenv;
              tvenv = new_tvs :: tctx.tvenv } in
            let (e, tctx) = visit ety tctx e in
            let tctx = { tctx with
              idenv = List.tl tctx.idenv;
              tvenv = List.tl tctx.tvenv } in
            match e with
              | Error e -> (Error e, tctx)
              | Ok e -> loop ((p, e) :: acc) tctx xs in
    loop [] tctx cases

  and lookup_var n ty tctx errf =
    match lookup_env n tctx.idenv with
      | None -> (Error [errf ()], tctx)
      | Some vty ->
        let (instty, ts, tctx) = instantiate tctx vty in
        let rules = (ty, instty) :: tctx.rules in
        let e = EVar ((n, 0L), vty) in
        let e = List.fold_left (fun e a -> EApp (e, EType a)) e ts in
        (Ok e, { tctx with rules })

  and visit ty tctx = function
    | Ast.Lit lit -> begin
      let resty = match lit with
        | LitInt _ -> Type.TInt
        | LitStr _ -> Type.TStr
        | LitChar _ -> Type.TStr in
      (Ok (ELit lit), { tctx with rules = (ty, resty) :: tctx.rules })
    end
    | Ast.Var n ->
      lookup_var n ty tctx (fun () -> "unknown binding named " ^ n)
    | Ast.Tup xs -> begin
      let (shape, tctx) = gen_tuple_shape tctx xs in
      let tctx = { tctx with rules = (ty, TTup shape) :: tctx.rules } in

      let rec loop acc tctx = function
        | ([], []) -> (Ok (ETup (List.rev acc)), tctx)
        | (x :: xs, y :: ys) -> begin
          match visit x tctx y with
            | (Ok e, tctx) -> loop (e :: acc) tctx (xs, ys)
            | error -> error
        end
        | _ -> failwith "IMPOSSIBLE DIMENSION MISMATCH" in
      loop [] tctx (shape, xs)
    end
    | Ast.List xs ->
      let ety = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let tctx = { tctx with rules = (ty, Type.tyList ety) :: tctx.rules } in
      let rec loop acc tctx = function
        | [] ->
          let gen_list acc =
            let foldf xs x = ECons ("(::)", [x; xs]) in
            List.fold_left foldf (ECons ("[]", [])) acc in
          (Result.map gen_list acc, tctx)
        | x :: xs ->
          let (x, tctx) = visit ety tctx x in
          match (acc, x) with
            | (Error p, Error q) -> loop (Error (p @ q)) tctx xs
            | (Error p, _) | (_, Error p) -> loop (Error p) tctx xs
            | (Ok acc, Ok x) -> loop (Ok (x :: acc)) tctx xs in
      loop (Ok []) tctx xs
    | Ast.Lam (ps, e) -> begin
      let sty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let ety = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let (cases, tctx) = visit_cases sty ety tctx [Ast.Detup ps, e] in
      match cases with
        | Error e -> (Error e, tctx)
        | Ok [(Ast.Detup ps, e)] -> begin
          let (subst, errors) = Type.unify tctx.subst tctx.rules in
          let tctx = { tctx with subst; rules = [] } in
          match errors with
            | _ :: _ -> (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)
            | [] ->
              match Type.expand subst sty with
                | (Type.TTup xs, subst) -> begin
                  let t = List.fold_right (fun a e -> Type.TArr (a, e)) xs ety in
                  let rules = (ty, t) :: tctx.rules in
                  let tctx = { tctx with rules; subst } in

                  let foldf (id, acc) ty =
                    let tmp = (("", id), ty) in
                    (Int64.succ id, (tmp, ty) :: acc) in
                  let (_, acc) = List.fold_left foldf (0L, []) xs in

                  let inputs = List.rev_map (fun (v, ty) -> (EVar v, ty)) acc in
                  let e = ConvCase.conv_case inputs [ps, e] in
                  (Ok (List.fold_left (fun e (v, _) -> ELam (v, e)) e acc), tctx)
                end
                | _ -> failwith "IMPOSSIBLE PATTERN TYPE"
        end
        | Ok _ -> failwith "IMPOSSIBLE NUMBER OF CASES"
    end
    | Ast.LamCase cases -> begin
      let sty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let ety = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let (cases, tctx) = visit_cases sty ety tctx cases in
      match cases with
        | Error e -> (Error e, tctx)
        | Ok cases ->
          let rules = (ty, Type.TArr (sty, ety)) :: tctx.rules in
          let (subst, errors) = Type.unify tctx.subst rules in
          let tctx = { tctx with subst; rules = [] } in
          match errors with
            | _ :: _ -> (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)
            | [] ->
              let (sty, subst) = Type.expand tctx.subst sty in
              let tctx = { tctx with subst } in

              let helper cases = List.map (fun (p, e) -> ([p], e)) cases in
              let e = ConvCase.conv_case [EVar (("", 0L), sty), sty] (helper cases) in
              (Ok (ELam ((("", 0L), sty), e)), tctx)
    end
    | Ast.App (f, v) -> begin
      let vty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in

      let (f, tctx) = visit (Type.TArr (vty, ty)) tctx f in
      let (v, tctx) = visit vty tctx v in
      match (f, v) with
        | (Ok f, Ok v) -> (Ok (EApp (f, v)), tctx)
        | _ -> (Error (merge_errors [f; v]), tctx)
    end
    | Ast.Unary (op, e) -> begin
      let ety = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in

      let (op, tctx) =
          let name = match op with
            | "-" -> "not" | "!" -> "negate"
            | op -> "(" ^ op ^ ")" in
          let ty = Type.TArr (ety, ty) in
          lookup_var name ty tctx (fun () -> "unknown unary operator " ^ op) in
      let (e, tctx) = visit ety tctx e in
      match (op, e) with
        | (Ok op, Ok e) -> (Ok (EApp (op, e)), tctx)
        | _ -> (Error (merge_errors [op; e]), tctx)
    end
    | Ast.Binary ("&&", p, q) -> begin
      let (p, tctx) = visit Type.tyBool tctx p in
      let (q, tctx) = visit Type.tyBool tctx q in
      match (p, q) with
        | (Ok p, Ok q) ->
          let e = ECase (p, [
            PatDecons ("True", []), q;
            PatDecons ("False", []), ECons ("False", [])]) in
          (Ok e, tctx)
        | _ -> (Error (merge_errors [p; q]), tctx)
    end
    | Ast.Binary ("||", p, q) -> begin
      let (p, tctx) = visit Type.tyBool tctx p in
      let (q, tctx) = visit Type.tyBool tctx q in
      match (p, q) with
        | (Ok p, Ok q) ->
          let e = ECase (p, [
            PatDecons ("True", []), ECons ("True", []);
            PatDecons ("False", []), q]) in
          (Ok e, tctx)
        | _ -> (Error (merge_errors [p; q]), tctx)
    end
    | Ast.Binary (op, p, q) -> begin
      let pty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let qty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in

      let (op, tctx) =
        let name = "(" ^ op ^ ")" in
        let ty = Type.TArr (pty, Type.TArr (qty, ty)) in
        lookup_var name ty tctx (fun () -> "unknown binary operator " ^ op) in
      let (p, tctx) = visit pty tctx p in
      let (q, tctx) = visit qty tctx q in
      match (op, p, q) with
        | (Ok op, Ok p, Ok q) -> (Ok (EApp (EApp (op, p), q)), tctx)
        | _ -> (Error (merge_errors [op; p; q]), tctx)
    end
    | Ast.Case (s, cases) -> begin
      let sty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let (s, tctx) = visit sty tctx s in
      match s with
        | Error e -> (Error e, tctx)
        | Ok s ->
          let (cases, tctx) = visit_cases sty ty tctx cases in
          match cases with
            | Error e -> (Error e, tctx)
            | Ok cases ->
              let (subst, errors) = Type.unify tctx.subst tctx.rules in
              let tctx = { tctx with subst; rules = [] } in
              match errors with
                | _ :: _ -> (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)
                | [] ->
                  let (sty, subst) = Type.expand tctx.subst sty in
                  let tctx = { tctx with subst } in

                  let helper cases = List.map (fun (p, e) -> ([p], e)) cases in
                  (Ok (ConvCase.conv_case [s, sty] (helper cases)), tctx)
    end
    | Ast.Cond (k, t, f) -> begin
      let (k, tctx) = visit Type.tyBool tctx k in
      let (t, tctx) = visit ty tctx t in
      let (f, tctx) = visit ty tctx f in
      match (k, t, f) with
        | (Ok k, Ok t, Ok f) ->
          let e = ECase (k, [PatDecons ("True", []), t; PatDecons ("False", []), f]) in
          (Ok e, tctx)
        | _ -> (Error (merge_errors [k; t; f]), tctx)
    end
    | Ast.ExprTyped (e, annot) -> begin
      (* solve the type first to help resolve ambiguous data constructors *)
      let (annot, tctx) = visit_ast_type true None tctx annot in
      match annot with
        | Error p -> (Error p, tctx)
        | Ok (annotty, kind, _) ->
          let rules = (kind, Type.TKind) :: (annotty, ty) :: tctx.rules in
          let (subst, errors) = Type.unify tctx.subst rules in
          let tctx = { tctx with subst; rules = [] } in
          match errors with
            | [] -> visit ty tctx e
            | _ ->
              (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)
    end
    | _ -> (Error ["Not implemented yet"], tctx) in

  visit ty tctx ast

let visit_top_expr (tctx : tctx) (ast : Ast.ast_expr) =
  let resty = Type.TVar ("", tctx.id)
  and tctx = { tctx with id = Int64.succ tctx.id } in
  match visit_expr resty tctx ast with
    | (Error e, _) -> Error e
    | (Ok ast, tctx) ->
      let (subst, errors) = Type.unify tctx.subst tctx.rules in
      match errors with
        | _ :: _ ->
          Error (List.map (Type.explain ~env:(Some subst)) errors)
        | [] ->
          let (resty, subst) = Type.expand subst resty in
          Ok (ast, resty, { tctx with subst; rules = [] })

let visit_toplevel (tctx : tctx) (ast : Ast.ast_toplevel) =
  match ast with
    | Ast.TopAlias aliases ->
      let rec loop tctx map errors = function
        | [] ->
          if errors = [] then
            let tctors = merge_map tctx.tctors map in
            Ok { tctx with tctors }
          else Error (List.rev errors)
        | x :: xs ->
          match visit_alias tctx x with
            | Error e -> Error e
            | Ok (n, t, k, tctx) ->
              let updatef = function
                | None -> Some (t, k)
                | t -> t in
              let next = StrMap.update n updatef map in
              if next == map then
                loop tctx next (("duplicate type alias " ^ n) :: errors) xs
              else
                loop tctx next errors xs in
      loop tctx StrMap.empty [] aliases
    | Ast.TopExpr e -> begin
      match visit_top_expr tctx e with
        | Error e -> Error e
        | Ok (_, _, tctx) -> Ok tctx
    end
    | _ -> Error ["NOT IMPLEMENTED YET"]

let visit_prog (tctx : tctx) (ast : Ast.ast_toplevel list) =
  let rec loop tctx = function
    | [] -> Ok tctx
    | x :: xs ->
      match visit_toplevel tctx x with
        | Error e -> Error e
        | Ok tctx -> loop tctx xs in
  loop tctx ast