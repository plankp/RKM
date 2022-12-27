module StrMap = Map.Make (String)
module V = VarInfo

type tkmap = (Type.t * Type.t) StrMap.t

type tctx = {
  id : Int64.t;
  tctors : tkmap;
  dctors : Type.variant StrMap.t;
  tvenv : tkmap list;
  idenv : Type.t StrMap.t list;
  rules : (Type.t * Type.t) list;
  subst : Type.t V.Map.t;
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

  dctors = map_of_list [
    "True", Type.varBool;
    "False", Type.varBool;
    "(::)", Type.varList;
  ];

  idenv = [];
  tvenv = [];
  rules = [];
  subst = V.Map.empty;
}

let free_ctx (tctx : tctx) : V.Set.t * tctx =
  let fold_id _ t (fv, subst) =
    let (t, subst) = Type.expand subst t in
    (Type.free_vars ~acc:fv t, subst) in
  let fold_tv _ (t, _) (fv, subst) =
    let (t, subst) = Type.expand subst t in
    (Type.free_vars ~acc:fv t, subst) in
  let foldf_list hof list init =
    let foldf init m = StrMap.fold hof m init in
    List.fold_left foldf init list in

  let fv = V.Set.empty in
  let subst = tctx.subst in
  let (fv, subst) = foldf_list fold_id tctx.idenv (fv, subst) in
  let (fv, subst) = foldf_list fold_tv tctx.tvenv (fv, subst) in
  (fv, { tctx with subst })

let unify_ctx (tctx : tctx) =
  let (subst, errors) = Type.unify tctx.subst tctx.rules in
  let tctx = { tctx with subst; rules = [] } in
  match errors with
    | [] -> (Ok (), tctx)
    | _ -> (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)

let ( let< ) o f =
  match o with
    | (Error e, tctx) -> (Error e, tctx)
    | (Ok v, tctx) -> f (v, tctx)

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
      loop tctx (fresh :: acc) (V.Map.add q fresh map) t
    | t ->
      let t =
        if V.Map.is_empty map then t
        else Type.eval map V.Set.empty t in
      (t, List.rev acc, tctx) in
  loop tctx [] V.Map.empty t

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

let collect_decl_tvs (tctx : tctx) (tvargs : string list) =
  let rec loop map acc errors tctx = function
    | [] ->
      if errors = [] then (Ok (map, List.rev acc), tctx)
      else (Error (List.rev errors), tctx)
    | x :: xs ->
      let name = (x, 0L) in
      let kind = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let updatef = function
        | None -> Some (Type.TRigid name, kind)
        | t -> t in
      let next = StrMap.update x updatef map in
      if next == map then
        loop next acc (("duplicate type variable " ^ x) :: errors) tctx xs
      else loop next ((name, kind) :: acc) errors tctx xs in
  loop StrMap.empty [] [] tctx tvargs

let visit_alias (tctx : tctx) ((n, args, t) : Ast.ast_alias) =
  if tctx.tvenv <> [] then failwith "TVENV NOT EMPTY?";
  if tctx.rules <> [] then failwith "RULES NOT EMPTY?";

  match collect_decl_tvs tctx args with
    | (Error e, _) -> Error e
    | (Ok (map, args), tctx) ->
      let open Type in
      let tctx = { tctx with tvenv = [map] } in
      match visit_ast_type false None tctx t with
        | (Error e, _) -> Error e
        | (Ok (t, k, _), tctx) ->
          let (subst, errors) = unify V.Map.empty tctx.rules in
          let tctx = { tctx with tvenv = []; rules = [] } in
          match errors with
            | _ :: _ -> Error (List.map (explain ~env:(Some subst)) errors)
            | [] ->
              let (k, subst) = expand subst k in
              let foldf (q, qk) (t, k, subst) =
                let (qk, subst) = expand subst qk in
                (TQuant (q, t), TArr (qk, k), subst) in
              let (t, k, _) = List.fold_right foldf args (t, k, subst) in
              let (qs, k) = Type.gen V.Set.empty k in
              let k = List.fold_right (fun q k -> Type.TQuant (q, k)) qs k in
              Ok (n, t, k, tctx)

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

let lookup_dctor n ty tctx =
  let (subst, errors) = Type.unify tctx.subst tctx.rules in
  let tctx = { tctx with subst; rules = [] } in
  match errors with
    | _ :: _ -> (Error (List.map (Type.explain ~env:(Some subst)) errors), tctx)
    | [] ->
      let (ty, subst) = Type.shallow_subst tctx.subst ty in
      let tctx = { tctx with subst } in
      let (ctor, ty, tctx) = match Type.normalize ty with
        | TCons (TCtorVar v, args) -> (Type.inst_case v n args, ty, tctx)
        | _ ->
          match StrMap.find_opt n tctx.dctors with
            | None -> (None, ty, tctx)
            | Some v ->
              let foldf (acc, tctx) _ =
                let fresh = Type.TVar ("", tctx.id)
                and tctx = { tctx with id = Int64.succ tctx.id } in
                (fresh :: acc, tctx) in
              let (args, tctx) = List.fold_left foldf ([], tctx) v.quants in
              let args = List.rev args in
              (Type.inst_case v n args, Type.TCons (TCtorVar v, args), tctx) in
      match ctor with
        | None -> (Error ["unknown data constructor named " ^ n], tctx)
        | Some ctor -> (Ok (ctor, ty), tctx)

let visit_pat (ty : Type.t) (next : tkmap) (tctx : tctx) (ast : Ast.ast_pat) =
  let rec visit captures next ty tctx = function
    | Ast.Cap None ->
      (Ok (Ast.Cap None, captures), next, tctx)
    | Ast.Cap (Some n) -> begin
      match StrMap.find_opt n captures with
        | Some _ -> (Error ["repeated capture of " ^ n], next, tctx)
        | None -> (Ok (Ast.Cap (Some n), StrMap.add n ty captures), next, tctx)
    end
    | Ast.Match lit as t -> begin
      let resty = match lit with
        | LitInt _ -> Type.TInt
        | LitStr _ -> Type.TStr
        | LitChar _ -> Type.TChr in
      let rules = (ty, resty) :: tctx.rules in
      (Ok (t, captures), next, { tctx with rules })
    end
    | Ast.Decons (k, ys) -> begin
      let (ctor_info, tctx) = lookup_dctor k ty tctx in
      match ctor_info with
        | Error e -> (Error e, next, tctx)
        | Ok (xs, resty) ->
          let rec loop acc captures next tctx = function
            | ([], []) ->
              let tctx = { tctx with rules = (ty, resty) :: tctx.rules } in
              (Ok (Ast.Decons (k, List.rev acc), captures), next, tctx)
            | (x :: xs, y :: ys) -> begin
              match visit captures next x tctx y with
                | (Ok (p, captures), next, tctx) ->
                  loop (p :: acc) captures next tctx (xs, ys)
                | error -> error
            end
            | _ -> (Error ["data constructor arity mismatch"], next, tctx) in
          loop [] captures next tctx (xs, ys)
    end
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
          visit captures next ty { tctx with rules } p
    end in

  match visit StrMap.empty next ty tctx ast with
    | (Error e, _, tctx) -> (Error e, tctx)
    | (Ok (p, captures), next, tctx) -> (Ok (p, captures, next), tctx)

let organize_vdefs (vdefs : Ast.ast_vdef list) =
  let rec order m acc = function
    | [] ->
      (* anything left only has type annotation so order does not matter, but
       * prefer putting it near the front *)
      let foldf n (t, _) acc = (n, t, []) :: acc in
      Ok (StrMap.fold foldf m (List.rev acc))
    | Ast.DefValue (n, _, _) :: xs -> begin
      (* if there's a value definition, we want to order by encounter order *)
      match StrMap.find_opt n m with
        | None -> order m acc xs (* already handled *)
        | Some (_, None) -> failwith "IMPOSSIBLE MISSING VALUE DEFINITION"
        | Some (t, Some (_, tl)) ->
          order (StrMap.remove n m) ((n, t, List.rev tl) :: acc) xs
    end
    | _ :: xs -> order m acc xs in

  let rec collect m = function
    | [] -> order m [] vdefs
    | Ast.DefAnnot (n, annot) :: xs -> begin
      match StrMap.find_opt n m with
        | Some (Some _, _) -> Error ["duplicate type annotation for " ^ n]
        | Some (None, defs) ->
          collect (StrMap.add n (Some annot, defs) m) xs
        | None ->
          collect (StrMap.add n (Some annot, None) m) xs
    end
    | Ast.DefValue (n, args, e) :: xs -> begin
      let argc = List.length args in
      match StrMap.find_opt n m with
        | Some (t, Some (k, defs)) ->
          if argc = 0 then Error ["duplicate definition for " ^ n]
          else if argc <> k then Error ["argument length mismatch for " ^ n]
          else
            collect (StrMap.add n (t, Some (k, (args, e) :: defs)) m) xs
        | Some (t, None) ->
          collect (StrMap.add n (t, Some (argc, [args, e])) m) xs
        | None ->
          collect (StrMap.add n (None, Some (argc, [args, e])) m) xs
    end in
  collect StrMap.empty vdefs

let rec visit_cases sty ety tctx cases =
  let rec loop acc tctx = function
    | [] -> (Ok (List.rev acc), tctx)
    | (p, e) :: xs ->
      let< ((p, new_ids, new_tvs), tctx) = visit_pat sty StrMap.empty tctx p in
      let tctx = { tctx with
        idenv = new_ids :: tctx.idenv;
        tvenv = new_tvs :: tctx.tvenv } in
      let (e, tctx) = visit_expr ety tctx e in
      let tctx = { tctx with
        idenv = List.tl tctx.idenv;
        tvenv = List.tl tctx.tvenv } in
      let< (e, tctx) = (e, tctx) in
      loop ((p, e) :: acc) tctx xs in
  loop [] tctx cases

and visit_generalized_lam ty tctx (mat : (Ast.ast_pat list * Ast.ast_expr) list) =
  let sty = Type.TVar ("", tctx.id)
  and tctx = { tctx with id = Int64.succ tctx.id } in
  let ety = Type.TVar ("", tctx.id)
  and tctx = { tctx with id = Int64.succ tctx.id } in

  (*
   * ordinary lambdas  | lambda cases  | generalized lambdas
   * \p11 p12... -> e1 | \p11 -> e1    | \p11 p12... -> e1
   *                   |  p21 -> e2... |  p21 p22... -> e2...
   *
   * the idea is to view generalized lambdas as this:
   * \x1 x2... -> match x1, x2, ... with p11, p12, ... -> e1
   *                                     p21, p22, ... -> e2...
   *)

  let proj_pack (ps, e) = (Ast.Detup ps, e) in
  let proj_unpack = function
    | (Ast.Detup ps, e) -> (ps, e)
    | _ -> failwith "IMPOSSIBLE GENERALIZE LAM PATTERN CASE" in

  let mat = List.map proj_pack mat in
  let< (mat, tctx) = visit_cases sty ety tctx mat in
  let< ((), tctx) = unify_ctx tctx in
  match Type.expand tctx.subst sty with
    | (Type.TTup xs, subst) -> begin
      let t = List.fold_right (fun a e -> Type.TArr (a, e)) xs ety in
      let rules = (ty, t) :: tctx.rules in
      let tctx = { tctx with rules; subst } in

      let foldf (id, acc) ty =
        let tmp = (("", id), ty) in
        (Int64.succ id, (tmp, ty) :: acc) in
      let (id, acc) = List.fold_left foldf (0L, []) xs in

      let inputs = List.rev_map (fun (v, ty) -> (Expr.EVar v, ty)) acc in
      let mat = List.map proj_unpack mat in
      let e = ConvCase.conv id inputs mat in
      (Ok (List.fold_left (fun e (v, _) -> Expr.ELam (v, e)) e acc), tctx)
    end
    | _ -> failwith "IMPOSSIBLE GENERALIZED LAM PATTERN TYPE"

and visit_vdefs (recur : bool) (tctx : tctx) (vb : Ast.ast_vdef list) =
  let rec proc_exprs new_ids ds acc tctx = function
    | [] ->
      let rec validate acc = function
        | [] -> (Ok (new_ids, acc), tctx)
        | (_, i) as x :: xs ->
          if not recur || Expr.is_valid_rec ds i then validate (x :: acc) xs
          else (Error ["Recursive binding cannot have initializer of this form"], tctx) in
      validate [] acc
    | (n, None, defs) :: xs -> begin
      let bty = StrMap.find n new_ids in
      let< (e, tctx) = visit_generalized_lam bty tctx defs in
      let n = (n, 0L) in
      proc_exprs new_ids (V.Set.add n ds) (((n, bty), e) :: acc) tctx xs
    end
    | (n, Some _, defs) :: xs -> begin
      let infty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let< (e, tctx) = visit_generalized_lam infty tctx defs in

      (* generalize the inferred type *)
      let< ((), tctx) = unify_ctx tctx in
      let (monos, tctx) = free_ctx tctx in
      let (infty, subst) = Type.expand tctx.subst infty in
      let tctx = { tctx with subst } in
      let (infty, tctx) =
        if Expr.is_syntactic_value e then begin
          let (infty, subst) = Type.expand tctx.subst infty in
          let tctx = { tctx with subst } in
          let (qs, infty) = Type.gen monos infty in
          (List.fold_right (fun q t -> Type.TQuant (q, t)) qs infty, tctx)
        end else (infty, tctx) in

      let qt = StrMap.find n new_ids in
      if Type.is_general_enough infty qt then
        (* then we register the annotated type *)
        let n = (n, 0L) in
        proc_exprs new_ids (V.Set.add n ds) (((n, qt), e) :: acc) tctx xs
      else
        (Error ["initializer is not general enough"], tctx)
    end in

  match organize_vdefs vb with
    | Error e -> (Error e, tctx)
    | Ok vb ->
      let rec fill_scope new_ids tctx = function
        | [] ->
          if recur then
            let tctx = { tctx with idenv = new_ids :: tctx.idenv } in
            let (q, tctx) = proc_exprs new_ids V.Set.empty [] tctx vb in
            let tctx = { tctx with idenv = List.tl tctx.idenv } in
            (q, tctx)
          else proc_exprs new_ids V.Set.empty [] tctx vb
        | (n, _, []) :: _ -> (Error ["missing implementation for " ^ n], tctx)
        | (n, None, _) :: xs ->
          let bty = Type.TVar ("", tctx.id)
          and tctx = { tctx with id = Int64.succ tctx.id } in
          fill_scope (StrMap.add n bty new_ids) tctx xs
        | (n, Some annot, _) :: xs ->
          let< ((bty, kind, _), tctx) = visit_ast_type true (Some StrMap.empty) tctx annot in
          let rules = (kind, Type.TKind) :: tctx.rules in
          let< ((), tctx) = unify_ctx { tctx with rules } in
          let (monos, tctx) = free_ctx tctx in

          let (quants, bty) = Type.gen monos bty in
          let qt = List.fold_right (fun q t -> Type.TQuant (q, t)) quants bty in
          fill_scope (StrMap.add n qt new_ids) tctx xs in
    fill_scope StrMap.empty tctx vb

and visit_expr (ty : Type.t) (tctx : tctx) (ast : Ast.ast_expr) =
  let open Expr in
  let rec lookup_var n ty tctx errf =
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
        | LitChar _ -> Type.TChr in
      let rules = (ty, resty) :: tctx.rules in
      (Ok (ELit lit), { tctx with rules })
    end
    | Ast.Var n ->
      lookup_var n ty tctx (fun () -> "unknown binding named " ^ n)
    | Ast.Tup xs -> begin
      let (shape, tctx) = gen_tuple_shape tctx xs in
      let tctx = { tctx with rules = (ty, TTup shape) :: tctx.rules } in

      let rec loop acc tctx = function
        | ([], []) -> (Ok (ETup (List.rev acc)), tctx)
        | (x :: xs, y :: ys) ->
          let< (e, tctx) = visit x tctx y in
          loop (e :: acc) tctx (xs, ys)
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
    | Ast.Cons (k, ys) -> begin
      let< ((xs, resty), tctx) = lookup_dctor k ty tctx in
      let rec loop acc tctx = function
        | ([], []) ->
          let tctx = { tctx with rules = (ty, resty) :: tctx.rules } in
          (Ok (ECons (k, List.rev acc)), tctx)
        | (x :: xs, y :: ys) ->
          let< (e, tctx) = visit x tctx y in
          loop (e :: acc) tctx (xs, ys)
        | (remaining, []) ->
          (* promote the ctor into a function then partial apply it *)
          let rec promote lift id = function
            | [] ->
              let e = ECons (k, List.rev_map (fun v -> EVar v) lift) in
              let e = List.fold_left (fun e a -> ELam (a, e)) e lift in
              let e = List.fold_right (fun a e -> EApp (e, a)) acc e in
              let resty = List.fold_right (fun a e -> Type.TArr (a, e)) remaining resty in
              (Ok e, { tctx with rules = (ty, resty) :: tctx.rules })
            | x :: xs -> promote ((("", id), x) :: lift) (Int64.succ id) xs in
          promote [] 0L xs
        | _ -> (Error ["data constructor arity mismatch"], tctx) in
      loop [] tctx (xs, ys)
    end
    | Ast.Lam (ps, e) ->
      visit_generalized_lam ty tctx [ps, e]
    | Ast.LamCase cases ->
      visit_generalized_lam ty tctx (List.map (fun (p, e) -> ([p], e)) cases)
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
    | Ast.Let (vb, e) -> begin
      let< ((new_ids, acc), tctx) = visit_vdefs false tctx vb in
      let tctx = { tctx with idenv = new_ids :: tctx.idenv } in
      let (e, tctx) = visit ty tctx e in
      let tctx = { tctx with idenv = List.tl tctx.idenv } in
      match e with
        | Error e -> (Error e, tctx)
        | Ok e ->
          (* rewrite it into a series of single nonrec lets *)
          let acc = List.rev_map (fun (((n, _), ty), i) -> (n, ty, i)) acc in
          let e = List.fold_left (fun e (n, ty, _) -> ELet (NonRec (((n, 0L), ty), EVar ((n, 1L), ty)), e)) e acc in
          let e = List.fold_left (fun e (n, ty, i) -> ELet (NonRec (((n, 1L), ty), i), e)) e acc in
          (Ok e, tctx)
    end
    | Ast.LetRec (vb, e) -> begin
      let< ((new_ids, acc), tctx) = visit_vdefs true tctx vb in
      let tctx = { tctx with idenv = new_ids :: tctx.idenv } in
      let (e, tctx) = visit ty tctx e in
      let tctx = { tctx with idenv = List.tl tctx.idenv } in
      match e with
        | Error e -> (Error e, tctx)
        | Ok e -> (Ok (ELet (Rec acc, e)), tctx)
    end
    | Ast.Case (s, cases) -> begin
      let sty = Type.TVar ("", tctx.id)
      and tctx = { tctx with id = Int64.succ tctx.id } in
      let< (s, tctx) = visit sty tctx s in
      let< (cases, tctx) = visit_cases sty ty tctx cases in
      let< ((), tctx) = unify_ctx tctx in
      let (sty, subst) = Type.expand tctx.subst sty in
      let tctx = { tctx with subst } in

      let helper cases = List.map (fun (p, e) -> ([p], e)) cases in
      (Ok (ConvCase.conv 0L [s, sty] (helper cases)), tctx)
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
      let< ((annotty, kind, _), tctx) = visit_ast_type true None tctx annot in
      let rules = (kind, Type.TKind) :: (annotty, ty) :: tctx.rules in
      visit ty { tctx with rules } e
    end in

  visit ty tctx ast

let visit_top_expr (tctx : tctx) (ast : Ast.ast_expr) =
  let resty = Type.TVar ("", tctx.id)
  and tctx = { tctx with id = Int64.succ tctx.id } in
  match visit_expr resty tctx ast with
    | (Error e, _) -> Error e
    | (Ok ast, tctx) ->
      match unify_ctx tctx with
        | (Error e, _) -> Error e
        | (Ok (), tctx) ->
          let (resty, subst) = Type.expand tctx.subst resty in
          Ok (ast, resty, { tctx with subst })

let visit_top_defs (tctx : tctx) (vb : Ast.ast_vdef list) =
  let (defs, tctx) = visit_vdefs true tctx vb in
  match defs with
    | Error e -> Error e
    | Ok (new_ids, _) -> Ok ({ tctx with idenv = new_ids :: tctx.idenv })

let visit_top_externs (tctx : tctx) (vb : Ast.ast_extern list) =
  let rec loop map tctx = function
    | [] ->
      let< ((), tctx) = unify_ctx tctx in
      (Ok map, tctx)
    | (n, annot, _) :: xs ->
      let< ((annot, kind, _), tctx) = visit_ast_type false None tctx annot in
      let tctx = { tctx with rules = (kind, Type.TKind) :: tctx.rules } in
      let updatef = function
        | None -> Some annot
        | t -> t in
      let next = StrMap.update n updatef map in
      if next == map then (Error ["duplicate extern definition " ^ n], tctx)
      else loop next tctx xs in

  match loop StrMap.empty tctx vb with
    | (Error e, _) -> Error e
    | (Ok m, tctx) ->
      Ok ({ tctx with idenv = m :: tctx.idenv })

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
    | Ast.TopDef defs ->
      visit_top_defs tctx defs
    | Ast.TopExtern defs ->
      visit_top_externs tctx defs
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