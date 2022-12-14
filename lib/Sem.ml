open Printf
module StrMap = Map.Make (String)
module V = VarInfo
module T = Type
module S = Solver
module C = Core

type tkmap = (T.t * T.t) StrMap.t
type vtmap = (C.expr * T.t) StrMap.t

type context = {
  id : Z.t;
  tctors : tkmap;
  dctors : T.variant StrMap.t;
  traits : (T.trait * T.t) StrMap.t;
  tvenv : tkmap list;
  idenv : vtmap list;

  fixed_tvars : V.Set.t;
  implications : (C.expr * T.pred) list;
}

type toplevel_analysis =
  | EvalExpr of Core.expr * T.t
  | AddTypes of tkmap
  | AddGlobl of (V.t * Core.expr) list
  | AddExtern of (T.t * string) StrMap.t

let map_of_list (list : (string * 'a) list) =
  list |> List.to_seq |> StrMap.of_seq

let core_context : context = {
  id = Z.zero;

  tctors = map_of_list ([
    "(->)", (TCons (TCtorArr, []), TArr (TKind, TArr (TKind, TKind)));
    "[]", (TCons (TCtorVar T.varList, []), TArr (TKind, TKind));
    "ref", (TCons (TCtorVar T.varRef, []), TArr (TKind, TKind));
    "Char", (TChr, TKind);
    "String", (TStr, TKind);
    "Int", (TInt, TKind);
    "Bool", (T.tyBool, TKind);
  ] : (string * (T.t * T.t)) list);

  dctors = map_of_list [
    "True", T.varBool;
    "False", T.varBool;
    "ref", T.varRef;
    "(::)", T.varList;
  ];

  traits = map_of_list [];

  idenv = [];
  tvenv = [];

  fixed_tvars = V.Set.empty;
  implications = [];
}

let ( let* ) = Result.bind

let merge_map m overwrite =
  StrMap.fold StrMap.add overwrite m

let mk_name (ctx : context) (name : string) : (V.t * context) =
  let id = Z.succ ctx.id in
  ((name, ctx.id), { ctx with id })

let mk_tvar (ctx : context) (name : string) : (T.t * context) =
  let (n, ctx) = mk_name ctx name in
  (T.TVar (n, ref None), ctx)

let inst (ctx : context) (t : T.t) : (T.t list * T.t * context) =
  let rec loop qs m ctx = function
    | T.TQuant ((n, id), t) ->
      let (new_tv, ctx) = mk_tvar ctx n in
      loop (new_tv :: qs) (V.Map.add (n, id) new_tv m) ctx t
    | t -> (List.rev qs, T.eval m V.Set.empty t, ctx) in
  loop [] V.Map.empty ctx t

let gen (ctx : context) (qs : T.tvinfo list) =
  let foldf (qs, m, ctx) ((n, id), _) =
    let (new_name, ctx) = mk_name ctx n in
    (new_name :: qs, V.Map.add (n, id) (T.TRigid new_name) m, ctx) in
  List.fold_left foldf ([], V.Map.empty, ctx) qs

let free_ctx (ctx : context) : V.Set.t =
  (* need to collect from both idenv and the tvenv *)
  let rec collect_tvenv acc = function
    | [] -> acc
    | x :: xs ->
      let foldf _ (t, _) acc = T.free_tvars ~acc t in
      collect_tvenv (StrMap.fold foldf x acc) xs in

  let rec collect_idenv acc = function
    | [] -> collect_tvenv acc ctx.tvenv
    | x :: xs ->
      let foldf _ (_, t) acc = T.free_tvars ~acc t in
      collect_idenv (StrMap.fold foldf x acc) xs in

  collect_idenv V.Set.empty ctx.idenv

let lookup_env (name : string) (env : 'a StrMap.t list) =
  let rec loop = function
    | [] -> None
    | x :: xs ->
      match StrMap.find_opt name x with
        | None -> loop xs
        | Some v -> Some v in
  loop env

let visit_ast_type (allow_ign : bool) (next : tkmap option) (ctx : context) (ast : Ast.ast_typ) =
  let rec visit next ctx = function
    | Ast.TypeIgn ->
      if allow_ign then
        let (ty, ctx) = mk_tvar ctx "_" in
        let (kind, ctx) = mk_tvar ctx "" in
        Ok (ty, kind, S.merge_cnst [], next, ctx)
      else Error ["unnamed type not allowed in this context"]
    | Ast.TypeVar n -> begin
      let tvenv = match next with
        | Some m -> m :: ctx.tvenv
        | None -> ctx.tvenv in
      match lookup_env n tvenv with
        | Some (ty, kind) -> Ok (ty, kind, S.merge_cnst [], next, ctx)
        | None ->
          match next with
            | None -> Error ["unknown type variable named " ^ n]
            | Some m ->
              let (ty, ctx) = mk_tvar ctx n in
              let (kind, ctx) = mk_tvar ctx "" in
              Ok (ty, kind, S.merge_cnst [], Some (StrMap.add n (ty, kind) m), ctx)
    end
    | Ast.TypeCtor n -> begin
      match StrMap.find_opt n ctx.tctors with
        | None -> Error ["unknown type constructor named " ^ n]
        | Some (ty, kind) ->
          let (_, kind, ctx) = inst ctx kind in
          Ok (ty, kind, S.merge_cnst [], next, ctx)
    end
    | Ast.TypeApp (p, q) ->
      let* (p, pkind, f1, next, ctx) = visit next ctx p in
      let* (q, qkind, f2, next, ctx) = visit next ctx q in
      let (kind, ctx) = mk_tvar ctx "" in
      let f3 = S.CnstEq (V.Set.empty, pkind, T.TArr (qkind, kind)) in
      Ok (T.TApp (p, q), kind, S.merge_cnst [f1; f2; f3], next, ctx)
    | Ast.TypeTup xs ->
      let rec loop elts rules next ctx = function
        | [] ->
          Ok (T.TTup (List.rev elts), T.TKind, S.merge_cnst rules, next, ctx)
        | x :: xs ->
          let* (x, xkind, f, next, ctx) = visit next ctx x in
          let rules = S.CnstEq (V.Set.empty, xkind, T.TKind) :: f :: rules in
          loop (x :: elts) rules next ctx xs in
      loop [] [] next ctx xs in

  let* (ty, kind, f, next, ctx) = visit next ctx ast in
  let ty = Type.normalize ty in
  if Type.contains_quant ty then Error ["unsaturated type aliases are not allowed"]
  else Ok (ty, kind, f, next, ctx)

let visit_contexted_type (ctx : context) (cnsts : Ast.ast_cnst list) (annot : Ast.ast_typ) =
  (* type variables in constraints must appear in the annotation *)
  let* (bty, kind, f, m, ctx) = visit_ast_type true (Some StrMap.empty) ctx annot in
  let m = Option.get m in
  let ctx = { ctx with tvenv = m :: ctx.tvenv } in
  let rec loop acc rules ctx = function
    | [] ->
      let ctx = { ctx with tvenv = List.tl ctx.tvenv } in
      Ok (List.rev acc, bty, kind, S.merge_cnst (f :: rules), m, ctx)
    | (n, [t]) :: xs -> begin
      match StrMap.find_opt n ctx.traits with
        | None -> Error ["unknown trait " ^ n]
        | Some (trait, argkind) ->
          let* (t, kind, f, _, ctx) = visit_ast_type false None ctx t in
          let rules = S.CnstEq (V.Set.empty, argkind, kind) :: f :: rules in
          loop (T.PredTrait (trait, t) :: acc) rules ctx xs
    end
    | _ -> Error ["multi parameter traits are not supported"] in
  loop [] [] ctx cnsts

let collect_decl_tvs (ctx : context) (tvargs : string list) =
  let rec loop map acc errors ctx = function
    | [] ->
      if errors = [] then Ok (map, List.rev acc, ctx)
      else Error (List.rev errors)
    | x :: xs ->
      let (name, ctx) = mk_name ctx x in
      let (kind, ctx) = mk_tvar ctx "" in
      let updatef = function
        | None -> Some (Type.TRigid name, kind)
        | t -> t in
      let next = StrMap.update x updatef map in
      if next == map then
        loop next acc (("duplicate type variable " ^ x) :: errors) ctx xs
      else loop next ((name, kind) :: acc) errors ctx xs in
  loop StrMap.empty [] [] ctx tvargs

let gen_tuple_shape ctx elts =
  let rec loop acc ctx = function
    | [] -> (List.rev acc, ctx)
    | _ :: xs ->
      let (ty, ctx) = mk_tvar ctx "" in
      loop (ty :: acc) ctx xs in
  loop [] ctx elts

let lookup_dctor n ty rules ctx =
  (* eagarly solve constraints *)
  match S.solve rules with
    | Error e -> Error (List.map S.explain e)
    | Ok rules ->
      let ty = T.normalize ty in
      let (ctor, ty, ctx) = match ty with
        | TCons (TCtorVar v, args) -> (T.inst_case v n args, ty, ctx)
        | _ ->
          match StrMap.find_opt n ctx.dctors with
            | None -> (None, ty, ctx)
            | Some (T.Variant info as v) ->
              let foldf (acc, ctx) _ =
                let (fresh, ctx) = mk_tvar ctx "" in
                (fresh :: acc, ctx) in
              let (args, ctx) = List.fold_left foldf ([], ctx) info.quants in
              let args = List.rev args in
              (T.inst_case v n args, T.TCons (TCtorVar v, args), ctx) in
      match ctor with
        | None -> Error ["unknown data constructor named " ^ n]
        | Some ctor -> Ok (ctor, ty, rules, ctx)

let translate_preds ?(preds = []) (ctx : context) (p : T.pred list) =
  let rec loop preds iargs ctx = function
    | x :: xs ->
      let (n, ctx) = mk_name ctx "@" in
      loop ((C.EVar n, x) :: preds) (n :: iargs) ctx xs
    | [] ->
      match iargs with
        | [x] -> ((fun e -> C.ELam (x, e)), preds, ctx)
        | _ ->
          let (n, ctx) = mk_name ctx "@" in
          ((fun e -> C.ELam (n, C.ECase (C.EVar n,
            [C.PatUnpack (List.rev iargs), e]))), preds, ctx) in
  loop preds [] ctx p

let visit_pat (ty : T.t) (rules : S.cnst list) (next : tkmap) (ctx : context) (ast : Ast.ast_pat) =
  let rec visit captures next ty rules ctx = function
    | Ast.Cap None as p ->
      Ok (p, rules, captures, next, ctx)
    | Ast.Cap (Some n) as p -> begin
      match StrMap.find_opt n captures with
        | Some _ -> Error ["repeated capture of " ^ n]
        | None ->
          let captures = StrMap.add n (C.EVar (n, Z.zero), ty) captures in
          Ok (p, rules, captures, next, ctx)
    end

    | Ast.Match lit as p ->
      let resty = match lit with
        | LitInt _ -> Type.TInt
        | LitStr _ -> Type.TStr
        | LitChar _ -> Type.TChr in
      Ok (p, S.CnstEq (ctx.fixed_tvars, ty, resty) :: rules, captures, next, ctx)

    | Ast.Decons (k, ys) ->
      let* (xs, resty, rules, ctx) = lookup_dctor k ty rules ctx in
      let rec loop acc rules captures next ctx = function
        | ([], []) ->
          let rules = S.CnstEq (ctx.fixed_tvars, ty, resty) :: rules in
          Ok (Ast.Decons (k, List.rev acc), rules, captures, next, ctx)
        | (x :: xs, y :: ys) ->
          let* (p, rules, captures, next, ctx) = visit captures next x rules ctx y in
          loop (p :: acc) rules captures next ctx (xs, ys)
        | _ -> Error ["data constructor arity mismatch"] in
      loop [] rules captures next ctx (xs, ys)

    | Ast.Detup xs ->
      let rec loop acc rules captures next ctx = function
        | ([], []) -> Ok (Ast.Detup (List.rev acc), rules, captures, next, ctx)
        | (x :: xs, y :: ys) ->
          let* (p, rules, captures, next, ctx) =
            visit captures next x rules ctx y in
          loop (p :: acc) rules captures next ctx (xs, ys)
        | _ -> failwith "IMPOSSIBLE DIMENSION MISMATCH" in

      let (shape, ctx) = gen_tuple_shape ctx xs in
      let rules = S.CnstEq (ctx.fixed_tvars, ty, TTup shape) :: rules in
      loop [] rules captures next ctx (shape, xs)

    | Ast.Delist xs ->
      let (ety, ctx) = mk_tvar ctx "" in
      let rec loop acc rules captures next ctx = function
        | [] ->
          let p = Ast.Decons ("[]", []) in
          let p = List.fold_left (fun xs x -> Ast.Decons ("(::)", [x; xs])) p acc in
          Ok (p, rules, captures, next, ctx)
        | x :: xs ->
          let* (p, rules, captures, next, ctx) =
            visit captures next ety rules ctx x in
          loop (p :: acc) rules captures next ctx xs in
      let rules = S.CnstEq (ctx.fixed_tvars, ty, T.tyList ety) :: rules in
      loop [] rules captures next ctx xs

    | Ast.Alternate (p, q) ->
      (* need to make sure both subpats capture the same things *)
      let* (p, rules, pcap, next, ctx) = visit StrMap.empty next ty rules ctx p in
      let* (q, rules, qcap, next, ctx) = visit StrMap.empty next ty rules ctx q in
      let rec loop pkv qcap captures rules ctx =
        match pkv () with
          | Seq.Nil -> begin
            match StrMap.choose_opt qcap with
              | None -> Ok (Ast.Alternate (p, q), rules, captures, next, ctx)
              | Some (cap, _) -> Error ["binding " ^ cap ^ " is only captured on one branch"]
          end
          | Seq.Cons ((cap, (v, ty1)), tl) ->
            match StrMap.find_opt cap qcap with
              | None -> Error ["binding " ^ cap ^ " is only captured on one branch"]
              | Some (_, ty2) ->
                match StrMap.find_opt cap captures with
                  | Some _ -> Error ["repeated capture of " ^ cap]
                  | None ->
                    let rules = S.CnstEq (ctx.fixed_tvars, ty1, ty2) :: rules in
                    let qcap = StrMap.remove cap qcap in
                    let captures = StrMap.add cap (v, ty1) captures in
                    loop tl qcap captures rules ctx in
      loop (StrMap.to_seq pcap) qcap captures rules ctx

    | Ast.PatternTyped (p, annot) ->
      let* (annot, kind, f, q, ctx) = visit_ast_type true (Some next) ctx annot in
      let next = Option.get q in
      let rules = f
        :: S.CnstEq (V.Set.empty, kind, T.TKind)
        :: S.CnstEq (ctx.fixed_tvars, annot, ty)
        :: rules in
      visit captures next ty rules ctx p in

  visit StrMap.empty next ty rules ctx ast

let rec organize_vdefs (vdefs : Ast.ast_vdef list) =
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
    | Ast.DefAnnot (n, cnsts, annot) :: xs -> begin
      match StrMap.find_opt n m with
        | Some (Some _, _) -> Error ["duplicate type annotation for " ^ n]
        | Some (None, defs) ->
          collect (StrMap.add n (Some (cnsts, annot), defs) m) xs
        | None ->
          collect (StrMap.add n (Some (cnsts, annot), None) m) xs
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

and visit_cases sty rules ety ctx cases =
  let rec loop acc rules ctx = function
    | [] -> Ok (List.rev acc, rules, ctx)
    | (p, e) :: xs ->
      let* (p, rules, new_ids, new_tvs, ctx) =
        visit_pat sty rules StrMap.empty ctx p in
      let ctx = { ctx with
        idenv = new_ids :: ctx.idenv;
        tvenv = new_tvs :: ctx.tvenv } in
      let* (e, rules, ctx) = visit_expr ety rules ctx e in
      let ctx = { ctx with
        idenv = List.tl ctx.idenv;
        tvenv = List.tl ctx.tvenv } in
      loop ((p, e) :: acc) rules ctx xs in
  loop [] rules ctx cases

and visit_generalized_lam ty rules ctx (mat : (Ast.ast_pat list * Ast.ast_expr) list) =
  let (sty, ctx) = mk_tvar ctx "" in
  let (ety, ctx) = mk_tvar ctx "" in

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
    | _ -> failwith "IMPOSSIBLE GENERALIZE LAMBDA PATTERN CASE" in

  let mat = List.map proj_pack mat in
  let* (mat, rules, ctx) = visit_cases sty rules ety ctx mat in

  (* eagarly solve constraints *)
  match S.solve rules with
    | Error e -> Error (List.map S.explain e)
    | Ok rules ->
      let sty = T.unwrap sty in
      match sty with
        | T.TTup xs ->
          let t = List.fold_right (fun a e -> T.TArr (a, e)) xs ety in
          let rules = S.CnstEq (ctx.fixed_tvars, ty, t) :: rules in

          let foldf (id, acc) ty = (Z.succ id, (("", id), ty) :: acc) in
          let (id, acc) = List.fold_left foldf (Z.zero, []) xs in

          let inputs = List.rev_map (fun (v, ty) -> (C.EVar v, ty)) acc in
          let mat = List.map proj_unpack mat in
          let e = ConvCase.conv id inputs mat in
          Ok (List.fold_left (fun e (v, _) -> C.ELam (v, e)) e acc, rules, ctx)
        | _ -> failwith "IMPOSSIBLE GENERALIZED LAMBDA PATTERN TYPE"

and visit_vdefs (recur : bool) (rules : S.cnst list) (ctx : context) (vb : Ast.ast_vdef list) =
  let* vb = organize_vdefs vb in
  let monos = free_ctx ctx in

  let rec eval_init new_ids ds acc rules ctx = function
    | [] -> begin
      let generalize rules ctx rbinds =
        let no_pending = rules = [] in
        let rec loop new_ids acc rules ctx = function
          | [] -> Ok (new_ids, acc, rules, ctx)
          | (n, bty, annot_info, e) :: xs ->
            if not recur || C.is_valid_rec ds e then begin
              let monos =
                if C.is_syntactic_value e then monos
                else T.dangerous_vars ~acc:monos bty in
              match annot_info with
                | Some (preds, ta) ->
                  let f = S.CnstImply (preds, S.CnstEq (monos, ta, bty)) in
                  loop new_ids (((n, Z.zero), e) :: acc) (f :: rules) ctx xs
                | _ ->
                  if no_pending then
                    let qs = T.collect_free_tvars bty in
                    let filterf (n, _) = not @@ V.Set.mem n monos in
                    let (qs, m, ctx) = gen ctx (List.filter filterf qs) in
                    let bty = T.subst ~weak:m bty in
                    let qt = List.fold_left (fun t q -> T.TQuant (q, t)) bty qs in

                    let updatef = function
                      | Some (t, _) -> Some (t, qt)
                      | _ -> failwith "IMPOSSIBLE RECURSIVE PLACEHOLDER" in
                    let new_ids = StrMap.update n updatef new_ids in
                    loop new_ids (((n, Z.zero), e) :: acc) rules ctx xs
                  else
                    loop new_ids (((n, Z.zero), e) :: acc) rules ctx xs
            end else Error ["recursive binding cannot have initializer of this form"] in
        loop new_ids [] rules ctx rbinds in

      match S.solve rules with
        | Error e -> Error (List.map S.explain e)
        | Ok rules -> generalize rules ctx acc
    end
    | (n, None, defs) :: xs ->
      let (_, bty) = StrMap.find n new_ids in
      let* (e, rules, ctx) = visit_generalized_lam bty rules ctx defs in
      eval_init new_ids (V.Set.add (n, Z.zero) ds) ((n, bty, None, e) :: acc) rules ctx xs
    | (n, Some _, defs) :: xs ->
      let rec unpeel preds emitfs ctx = function
        | T.TQuant (_, t) -> unpeel preds emitfs ctx t
        | T.TPred (p, t) ->
          let (emitf, preds, ctx) = translate_preds ~preds ctx p in
          unpeel preds (emitf :: emitfs) ctx t
        | ta ->
          let (bty, ctx) = mk_tvar ctx "" in
          let old_implications = ctx.implications in
          let ctx = { ctx with implications = preds @ ctx.implications } in
          let* (e, rules, ctx) = visit_generalized_lam bty rules ctx defs in
          let ctx = { ctx with implications = old_implications } in
          let e = List.fold_left (fun e f -> f e) e emitfs in
          eval_init new_ids (V.Set.add (n, Z.zero) ds) ((n, bty, Some (preds, ta), e) :: acc) rules ctx xs in
      let (_, annot) = StrMap.find n new_ids in
      unpeel [] [] ctx annot in

  let rec fill_scope new_ids rules ctx = function
    | [] ->
      let old_fixed_tvars = ctx.fixed_tvars in
      let ctx = { ctx with fixed_tvars = monos } in
      let* (m, acc, rules, ctx) =
        if recur then
          let ctx = { ctx with idenv = new_ids :: ctx.idenv } in
          let* (m, acc, rules, ctx) = eval_init new_ids V.Set.empty [] rules ctx vb in
          let ctx = { ctx with idenv = List.tl ctx.idenv } in
          Ok (m, acc, rules, ctx)
        else eval_init new_ids V.Set.empty [] rules ctx vb in
      Ok (m, acc, rules, { ctx with fixed_tvars = old_fixed_tvars })
    | (n, _, []) :: _ -> Error ["missing implementation for " ^ n]
    | (n, None, _) :: xs ->
      let (bty, ctx) = mk_tvar ctx "" in
      let new_ids = StrMap.add n (C.EVar (n, Z.zero), bty) new_ids in
      fill_scope new_ids rules ctx xs
    | (n, Some (cnsts, annot), _) :: xs ->
      let* (preds, bty, kind, f, _, ctx) = visit_contexted_type ctx cnsts annot in
      let bty = if preds = [] then bty else T.TPred (preds, bty) in
      let rules = S.CnstEq (V.Set.empty, kind, T.TKind) :: rules in
      let qs = T.collect_free_tvars bty in
      let filterf (n, _) = not @@ V.Set.mem n monos in
      let (qs, m, ctx) = gen ctx (List.filter filterf qs) in
      let bty = T.subst ~weak:m bty in
      let qt = List.fold_left (fun t q -> T.TQuant (q, t)) bty qs in
      let new_ids = StrMap.add n (C.EVar (n, Z.zero), qt) new_ids in
      fill_scope new_ids (f :: rules) ctx xs in
  fill_scope StrMap.empty rules ctx vb

and lookup_var n ty ctx errf =
  match lookup_env n ctx.idenv with
    | None -> Error [errf ()]
    | Some (e, vty) ->
      let rec emit_arg iargs cnsts = function
        | p :: xs ->
          let (tc, dep) = C.mk_empty_hole () in
          let new_cnst = S.CnstImply (ctx.implications, S.CnstPred (dep, p)) in
          emit_arg (tc :: iargs) (new_cnst :: cnsts) xs
        | [] ->
          match iargs with
            | [x] -> (x, cnsts)
            | _ -> (C.ETup (List.rev iargs), cnsts) in

      let rec fill_implicits e rules ctx = function
        | T.TPred (p, t) ->
          let (p, rules) = emit_arg [] rules p in
          fill_implicits (C.EApp (e, p)) rules ctx t
        | t ->
          let rules = S.CnstEq (ctx.fixed_tvars, ty, t) :: rules in
          Ok (e, S.merge_cnst rules, ctx) in
      let (_, instty, ctx) = inst ctx vty in
      fill_implicits e [] ctx instty

and visit_expr (ty : T.t) (rules : S.cnst list) (ctx : context) = function
  | Ast.Lit lit ->
    let resty = match lit with
      | LitInt _ -> Type.TInt
      | LitStr _ -> Type.TStr
      | LitChar _ -> Type.TChr in
    Ok (C.ELit lit, S.CnstEq (ctx.fixed_tvars, ty, resty) :: rules, ctx)

  | Ast.Var n ->
    let* (e, f, ctx) = lookup_var n ty ctx (fun () -> "unknown binding named " ^ n) in
    Ok (e, f :: rules, ctx)

  | Ast.Tup xs ->
    let rec loop acc rules ctx = function
      | ([], []) -> Ok (C.ETup (List.rev acc), rules, ctx)
      | (x :: xs, y :: ys) ->
        let* (e, rules, ctx) = visit_expr x rules ctx y in
        loop (e :: acc) rules ctx (xs, ys)
      | _ -> failwith "IMPOSSIBLE DIMENSION MISMATCH" in

    let (shape, ctx) = gen_tuple_shape ctx xs in
    let rules = S.CnstEq (ctx.fixed_tvars, ty, TTup shape) :: rules in
    loop [] rules ctx (shape, xs)

  | Ast.List xs ->
    let (ety, ctx) = mk_tvar ctx "" in
    let rec loop acc rules ctx = function
      | [] ->
        let gen_list acc =
          let foldf xs x = C.ECons ("(::)", ty, [x; xs]) in
          List.fold_left foldf (C.ECons ("[]", ty, [])) acc in
        Ok (gen_list acc, rules, ctx)
      | x :: xs ->
        let* (x, rules, ctx) = visit_expr ety rules ctx x in
        loop (x :: acc) rules ctx xs in
    let rules = S.CnstEq (ctx.fixed_tvars, ty, T.tyList ety) :: rules in
    loop [] rules ctx xs

  | Ast.Cons (k, ys) ->
    let* (xs, resty, rules, ctx) = lookup_dctor k ty rules ctx in
    let rec loop acc rules ctx = function
      | ([], []) ->
        let rules = S.CnstEq (ctx.fixed_tvars, ty, resty) :: rules in
        Ok (C.ECons (k, resty, List.rev acc), rules, ctx)
      | (x :: xs, y :: ys) ->
        let* (e, rules, ctx) = visit_expr x rules ctx y in
        loop (e :: acc) rules ctx (xs, ys)
      | (remaining, []) ->
        (* promote the ctor into a function then partial apply it *)
        let rec promote lift id = function
          | [] ->
            let e = C.ECons (k, resty, List.rev_map (fun v -> C.EVar v) lift) in
            let e = List.fold_left (fun e a -> C.ELam (a, e)) e lift in
            let e = List.fold_right (fun a e -> C.EApp (e, a)) acc e in
            let resty = List.fold_right (fun a e -> T.TArr (a, e)) remaining resty in
            Ok (e, S.CnstEq (ctx.fixed_tvars, ty, resty) :: rules, ctx)
          | _ :: xs -> promote (("", id) :: lift) (Z.succ id) xs in
        promote [] Z.zero xs
      | _ -> Error ["data constructor arity mismatch"] in
    loop [] rules ctx (xs, ys)

  | Ast.Lam (ps, e) ->
    visit_generalized_lam ty rules ctx [ps, e]
  | Ast.LamCase cases ->
    visit_generalized_lam ty rules ctx (List.map (fun (p, e) -> ([p], e)) cases)

  | Ast.App (f, v) ->
    let (vty, ctx) = mk_tvar ctx "" in
    let* (f, rules, ctx) = visit_expr (T.TArr (vty, ty)) rules ctx f in
    let* (v, rules, ctx) = visit_expr vty rules ctx v in
    Ok (C.EApp (f, v), rules, ctx)

  | Ast.Unary (op, e) ->
    let (ety, ctx) = mk_tvar ctx "" in
    let* (op, f, ctx) =
      let name = match op with
        | "-" -> "negate" | "!" -> "not"
        | op -> "(" ^ op ^ ")" in
      let ty = T.TArr (ety, ty) in
      lookup_var name ty ctx (fun () -> "unknown unary operator " ^ op) in
    let* (e, rules, ctx) = visit_expr ety rules ctx e in
    Ok (C.EApp (op, e), f :: rules, ctx)

  | Ast.Binary ("=", p, q) ->
    let (ety, ctx) = mk_tvar ctx "" in
    let rules = S.CnstEq (ctx.fixed_tvars, ty, T.TTup []) :: rules in
    let* (p, rules, ctx) = visit_expr (T.tyRef ety) rules ctx p in
    let* (q, rules, ctx) = visit_expr ety rules ctx q in
    Ok (C.ESet (p, 0, q), rules, ctx)

  | Ast.Binary ("&&", p, q) ->
    let rules = S.CnstEq (ctx.fixed_tvars, ty, T.tyBool) :: rules in
    let* (p, rules, ctx) = visit_expr T.tyBool rules ctx p in
    let* (q, rules, ctx) = visit_expr T.tyBool rules ctx q in
    let e = C.ECase (p, [
      PatDecons ("True", []), q;
      PatDecons ("False", []), ECons ("False", T.tyBool, [])]) in
    Ok (e, rules, ctx)

  | Ast.Binary ("||", p, q) ->
    let rules = S.CnstEq (ctx.fixed_tvars, ty, T.tyBool) :: rules in
    let* (p, rules, ctx) = visit_expr T.tyBool rules ctx p in
    let* (q, rules, ctx) = visit_expr T.tyBool rules ctx q in
    let e = C.ECase (p, [
      PatDecons ("True", []), ECons ("True", T.tyBool, []);
      PatDecons ("False", []), q]) in
    Ok (e, rules, ctx)

  | Ast.Binary (op, p, q) ->
    let (pty, ctx) = mk_tvar ctx "" in
    let (qty, ctx) = mk_tvar ctx "" in
    let* (op, f, ctx) =
      let name = "(" ^ op ^ ")" in
      let ty = T.TArr (pty, T.TArr (qty, ty)) in
      lookup_var name ty ctx (fun () -> "unknown binary operator " ^ op) in
    let* (p, rules, ctx) = visit_expr pty rules ctx p in
    let* (q, rules, ctx) = visit_expr qty rules ctx q in
    Ok (C.EApp (C.EApp (op, p), q), f :: rules, ctx)

  | Ast.Seq [] ->
    Ok (C.ETup [], S.CnstEq (ctx.fixed_tvars, ty, T.TTup []) :: rules, ctx)
  | Ast.Seq (x :: xs) ->
    let rec loop acc rules ctx x = function
      | [] ->
        let* (x, rules, ctx) = visit_expr ty rules ctx x in
        let foldf e v = C.ELet (NonRec (("_", Z.zero), v), e) in
        Ok (List.fold_left foldf x acc, rules, ctx)
      | y :: xs ->
        let* (x, rules, ctx) = visit_expr (T.TTup []) rules ctx x in
        loop (x :: acc) rules ctx y xs in
    loop [] rules ctx x xs

  | Ast.Let (vb, e) ->
    let* (new_ids, acc, rules, ctx) = visit_vdefs false rules ctx vb in
    let ctx = { ctx with idenv = new_ids :: ctx.idenv } in
    let* (e, rules, ctx) = visit_expr ty rules ctx e in
    let ctx = { ctx with idenv = List.tl ctx.idenv } in

    (* rewrite it into a series of single nonrec lets *)
    let acc = List.rev_map (fun ((n, _), i) -> (n, i)) acc in
    let e = List.fold_left (fun e (n, _) -> C.ELet (NonRec ((n, Z.zero), EVar (n, Z.one)), e)) e acc in
    let e = List.fold_left (fun e (n, i) -> C.ELet (NonRec ((n, Z.one), i), e)) e acc in
    Ok (e, rules, ctx)

  | Ast.LetRec (vb, e) ->
    let* (new_ids, acc, rules, ctx) = visit_vdefs true rules ctx vb in
    let ctx = { ctx with idenv = new_ids :: ctx.idenv } in
    let* (e, rules, ctx) = visit_expr ty rules ctx e in
    let ctx = { ctx with idenv = List.tl ctx.idenv } in
    Ok (C.ELet (Rec acc, e), rules, ctx)

  | Ast.Case (s, cases) -> begin
    let (sty, ctx) = mk_tvar ctx "" in
    let* (s, rules, ctx) = visit_expr sty rules ctx s in
    let* (cases, rules, ctx) = visit_cases sty rules ty ctx cases in

    (* eagarly solve constraints *)
    match S.solve rules with
      | Error e -> Error (List.map S.explain e)
      | Ok rules ->
        let helper cases = List.map (fun (p, e) -> ([p], e)) cases in
        let tmp = ("", Z.zero) in
        let e = ConvCase.conv Z.one [C.EVar tmp, sty] (helper cases) in
        Ok (C.ELet (NonRec (tmp, s), e), rules, ctx)
  end

  | Ast.Cond (k, t, f) ->
    let* (k, rules, ctx) = visit_expr Type.tyBool rules ctx k in
    let* (t, rules, ctx) = visit_expr ty rules ctx t in
    let* (f, rules, ctx) = visit_expr ty rules ctx f in
    let e = C.ECase (k, [C.PatDecons ("True", []), t; C.PatDecons ("False", []), f]) in
    Ok (e, rules, ctx)

  | Ast.ExprTyped (e, annot) ->
    let* (annot, kind, f, _, ctx) = visit_ast_type true None ctx annot in
    let rules = f
      :: S.CnstEq (V.Set.empty, kind, T.TKind)
      :: S.CnstEq (ctx.fixed_tvars, annot, ty)
      :: rules in
    visit_expr ty rules ctx e

let visit_top_expr (ctx : context) (ast : Ast.ast_expr) =
  let (resty, ctx) = mk_tvar ctx "" in
  let* (ast, rules, ctx) = visit_expr resty [] ctx ast in
  match S.solve rules with
    | Error e -> Error (List.map S.explain e)
    | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
    | Ok [] -> Ok (C.normalize ast, resty, ctx)

let visit_top_defs (ctx : context) (vb : Ast.ast_vdef list) =
  let* (new_ids, acc, rules, ctx) = visit_vdefs true [] ctx vb in
  match S.solve rules with
    | Error e -> Error (List.map S.explain e)
    | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
    | Ok [] ->
      let mapf (b, i) = (b, C.normalize i) in
      Ok (List.map mapf acc, { ctx with idenv = new_ids :: ctx.idenv })

let visit_top_impl (ctx : context) ((cnsts, n, ty, vb): Ast.ast_impl) =
  if ctx.tvenv <> [] then failwith "TVENV NOT EMPTY?";
  if ctx.implications <> [] then failwith "IMPLICATIONS NOT EMPTY?";

  match StrMap.find_opt n ctx.traits with
    | None -> Error ["unknown trait " ^ n]
    | Some (T.Trait info, argkind) ->
      let* (preds, bty, kind, f, _, ctx) = visit_contexted_type ctx cnsts ty in
      let rules = [S.CnstEq (V.Set.empty, argkind, kind); f] in

      let qs = T.collect_free_tvars bty in
      let (qs, m, ctx) = gen ctx qs in
      let preds = List.map (T.subst_pred ~weak:m) preds in
      let bty = T.subst ~weak:m bty in
      let qt = if preds = [] then bty else T.TPred (preds, bty) in
      let qt = List.fold_left (fun t q -> T.TQuant (q, t)) qt qs in

      let (emitf, impls, ctx) =
        if preds = [] then ((fun x -> x), [], ctx)
        else translate_preds ctx preds in
      let name = sprintf "@$%s[%s]" info.name (T.to_string bty) in
      let* vb = organize_vdefs vb in
      let monos = free_ctx ctx in
      let rigid = V.Map.singleton info.quant bty in

      let rec eval_init entries remaining rules ctx = function
        | [] -> begin
          match StrMap.choose_opt remaining with
            | Some (k, _) -> Error ["missing implementation for field " ^ k]
            | None ->
              match S.solve rules with
                | Error e -> Error (List.map S.explain e)
                | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
                | Ok [] ->
                  let entries = entries
                    |> StrMap.to_seq
                    |> Seq.map snd
                    |> Seq.map C.normalize
                    |> List.of_seq in
                  let e = match entries with
                    | [x] -> x
                    | xs -> C.ETup xs in
                  Ok ([(name, Z.zero), emitf e], ctx)
        end

        | (n, _, []) :: _ -> Error ["missing implementation for " ^ n]
        | (_, Some _, _) :: _ -> Error ["explicit type annotation not allowed here"]
        | (n, None, defs) :: xs ->
          match StrMap.find_opt n remaining with
            | None -> Error ["trait " ^ info.name ^ " does not have field " ^ n]
            | Some annot ->
              let rec unpeel preds emitfs ctx = function
                | T.TPred (p, t) ->
                  let (emitf, preds, ctx) = translate_preds ~preds ctx p in
                  unpeel preds (emitf :: emitfs) ctx t
                | ta ->
                  let (bty, ctx) = mk_tvar ctx "" in
                  let ctx = { ctx with implications = preds } in
                  let* (e, rules, ctx) = visit_generalized_lam bty rules ctx defs in
                  let ctx = { ctx with implications = [] } in
                  let e = List.fold_left (fun e f -> f e) e emitfs in

                  match S.solve rules with
                    | Error e -> Error (List.map S.explain e)
                    | Ok rules ->
                      let monos =
                        if C.is_syntactic_value e then monos
                        else T.dangerous_vars ~acc:monos bty in
                      let f = S.CnstImply (impls, S.CnstEq (monos, ta, bty)) in
                      eval_init (StrMap.add n e entries) (StrMap.remove n remaining) (f :: rules) ctx xs in
              unpeel impls [] ctx (T.subst ~rigid annot) in

      (* assume this is correctly implemented *)
      info.allowed <- (name, qt) :: info.allowed;
      match eval_init StrMap.empty info.fields rules ctx vb with
        | Ok t -> Ok t
        | Error e ->
          (* undo the assumption on error to avoid using broken impls *)
          info.allowed <- List.tl info.allowed;
          Error e

let visit_top_trait (ctx : context) ((n, args, vb): Ast.ast_trait) =
  if ctx.tvenv <> [] then failwith "TVENV NOT EMPTY?";

  match args with
    | [] | _ :: _ :: _ -> Error ["multi parameter traits are not supported"]
    | [arg] ->
      let (argkind, ctx) = mk_tvar ctx "" in
      let tvenv = StrMap.singleton arg (T.TRigid (arg, Z.zero), argkind) in
      let ctx = { ctx with tvenv = [tvenv] } in
      let rec process_fields fields defs rules ctx = function
        | [] -> begin
          match S.solve rules with
            | Error e -> Error (List.map S.explain e)
            | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
            | Ok [] ->
              let trait = T.Trait {
                name = n;
                quant = (arg, Z.zero);
                fields = fields;
                allowed = [];
              } in

              (* aggressively ground all remaining kinds to * *)
              let foldf (_, r) _ = r := Some T.TKind in
              let () = T.fold_free_tvars foldf argkind () in
              let ctx = { ctx with
                traits = StrMap.add n (trait, argkind) ctx.traits;
                tvenv = [] } in

              let layout = defs |> StrMap.to_seq |> List.of_seq in
              let layout = match layout with
                | [x, _] ->
                  [(x, Z.zero), C.ELam (("", Z.zero), C.EVar ("", Z.zero))]
                | _ ->
                  let (_, unpacking) = List.fold_left (fun (id, acc) _ ->
                    (Z.succ id, ("", id) :: acc)) (Z.zero, []) layout in
                  let mapf (x, _) offset =
                    ((x, Z.zero), C.ELam (("", Z.zero), C.ECase (C.EVar ("", Z.zero),
                      [C.PatUnpack unpacking, C.EVar offset]))) in
                  List.map2 mapf layout unpacking in
              let mapf k (qs, ty) =
                let ty = T.TPred ([T.PredTrait (trait, T.TRigid (arg, Z.zero))], ty) in
                let ty = List.fold_left (fun t q -> T.TQuant (q, t)) ty qs in
                (C.EVar (k, Z.zero), T.TQuant ((arg, Z.zero), ty)) in
              let defs = StrMap.mapi mapf defs in
              Ok (layout, { ctx with idenv = defs :: ctx.idenv })
        end

        | (n, None, _) :: _ -> Error ["missing annotation for " ^ n]
        | (_, _, _ :: _) :: _ -> Error ["default implementation not allowed here"]
        | (n, Some (cnsts, annot), []) :: xs ->
          let* (preds, bty, kind, f, _, ctx) = visit_contexted_type ctx cnsts annot in
          let rules = S.CnstEq (V.Set.empty, kind, T.TKind) :: f :: rules in
          let qs = T.collect_free_tvars bty in
          let (qs, m, ctx) = gen ctx qs in
          let preds = List.map (T.subst_pred ~weak:m) preds in
          let bty = T.subst ~weak:m bty in
          let ty = if preds = [] then bty else T.TPred (preds, bty) in
          let updatef = function
            | None -> Some ty
            | t -> t in
          let next = StrMap.update n updatef fields in
          if next == fields then Error ["duplicate trait field " ^ n]
          else process_fields next (StrMap.add n (qs, ty) defs) rules ctx xs in

      let* vb = organize_vdefs vb in
      process_fields StrMap.empty StrMap.empty [] ctx vb

let visit_top_externs (ctx : context) (vb : Ast.ast_extern list) =
  let rec loop rules map ctx = function
    | [] -> begin
      match S.solve rules with
        | Error e -> Error (List.map S.explain e)
        | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
        | Ok [] -> Ok (map, ctx)
    end
    | (n, annot, extn) :: xs ->
      let* (annot, kind, f, _, ctx) = visit_ast_type false None ctx annot in
      let updatef = function
        | None -> Some (annot, extn)
        | t -> t in
      let next = StrMap.update n updatef map in
      if next == map then Error ["duplicate extern definition " ^ n]
      else loop (S.CnstEq (V.Set.empty, kind, T.TKind) :: f :: rules) next ctx xs in

  let* (m, ctx) = loop [] StrMap.empty ctx vb in
  let s = StrMap.mapi (fun k (t, _) -> (C.EVar (k, Z.zero), t)) m in
  Ok (m, { ctx with idenv = s :: ctx.idenv })

let visit_top_alias (ctx : context) (aliases : Ast.ast_alias list) =
  if ctx.tvenv <> [] then failwith "TVENV NOT EMPTY?";

  let open Type in
  let rec collect_cases rules new_decls new_cases new_aliases ctx = function
    | [] -> begin
      let normalize t = t |> subst ~rigid:new_aliases |> normalize in
      match S.solve rules with
        | Error e -> Error (List.map S.explain e)
        | Ok (_ :: _ as e) -> Error (List.map S.explain_remaining e)
        | Ok [] ->
          let ctx = { ctx with tvenv = [] } in
          let rec update_kinds new_types ctx = function
            | [] ->
              Ok (new_types, { ctx with dctors = merge_map ctx.dctors new_cases })

            | Ast.DefAlias (n, _, _) :: xs ->
              let (_, k) = StrMap.find n ctx.tctors in
              let t = V.Map.find (n, Z.minus_one) new_aliases |> normalize in
              let qs = collect_free_tvars k in
              let (qs, m, ctx) = gen ctx qs in
              let k = subst ~weak:m k in
              let k = List.fold_left (fun k q -> TQuant (q, k)) k qs in
              let tctors = StrMap.add n (t, k) ctx.tctors in
              let new_types = StrMap.add n (t, k) new_types in
              update_kinds new_types { ctx with tctors } xs

            | Ast.DefData (n, _, _) :: xs ->
              let (t, k) = StrMap.find n ctx.tctors in
              match t with
                | TCons (TCtorVar (Variant v), []) -> begin
                  try
                    let mapf _ (t : t list) =
                      let mapf t =
                        let t = normalize t in
                        if not @@ contains_quant t then t
                        else failwith "unsaturated type aliases are not allowed" in
                      Some (List.map mapf t) in
                    Hashtbl.filter_map_inplace mapf v.cases;

                    let qs = collect_free_tvars k in
                    let (qs, m, ctx) = gen ctx qs in
                    let k = subst ~weak:m k in
                    let k = List.fold_left (fun k q -> TQuant (q, k)) k qs in
                    let tctors = StrMap.add n (t, k) ctx.tctors in
                    let new_types = StrMap.add n (t, k) new_types in
                    update_kinds new_types { ctx with tctors } xs
                  with Failure e -> Error [e]
                end
                | _ -> failwith "IMPOSSIBLE NON-VARIANT CONTRUCTOR" in
          update_kinds StrMap.empty ctx aliases
    end

    | Ast.DefAlias (n, _, t) :: xs ->
      let (_, knot, args, tvenv) = StrMap.find n new_decls in
      let ctx = { ctx with tvenv = [tvenv] } in
      let* (t, k, f, _, ctx) = visit_ast_type false None ctx t in
      let rules = S.CnstEq (V.Set.empty, k, knot) :: f :: rules in
      let t = List.fold_right (fun (q, _) t -> TQuant (q, t)) args t in
      let new_aliases = V.Map.add (n, Z.minus_one) t new_aliases in
      collect_cases rules new_decls new_cases new_aliases ctx xs

    | Ast.DefData (n, _, cases) :: xs ->
      match StrMap.find n new_decls with
        | (TCons (TCtorVar (Variant info as v), []), knot, _, tvenv) ->
          let rec loop rules new_cases ctx = function
            | [] -> collect_cases rules new_decls new_cases new_aliases ctx xs
            | (k, args) :: xs ->
              let rec inner rules acc ctx = function
                | [] -> begin
                  if Hashtbl.mem info.cases k then
                    Error ["duplicate data constructor " ^ k]
                  else begin
                    Hashtbl.add info.cases k (List.rev acc);
                    loop rules (StrMap.add k v new_cases) ctx xs
                  end
                end
                | x :: xs ->
                  let* (t, k, f, _, ctx) = visit_ast_type false None ctx x in
                  inner (S.CnstEq (V.Set.empty, k, knot) :: f :: rules) (t :: acc) ctx xs in
              inner rules [] ctx args in
          loop rules new_cases { ctx with tvenv = [tvenv] } cases
        | _ -> failwith "IMPOSSIBLE NON-VARIANT CONSTRUCTOR FOR SUM TYPES" in

  let rec collect_names new_decls ctx = function
    | [] -> collect_cases [] new_decls StrMap.empty V.Map.empty ctx aliases
    | Ast.DefAlias (n, args, _) :: xs ->
      let* (tvenv, args, ctx) = collect_decl_tvs ctx args in
      let value = TRigid (n, Z.minus_one) in
      let (kind, ctx) = mk_tvar ctx "" in
      tail n args value kind tvenv new_decls ctx xs

    | Ast.DefData (n, args, _) :: xs ->
      let* (tvenv, args, ctx) = collect_decl_tvs ctx args in
      let value = TCons (TCtorVar (Variant {
        name = n;
        quants = List.map fst args;
        cases = Hashtbl.create 16;
      }), []) in
      tail n args value TKind tvenv new_decls ctx xs

  and tail n args value kind tvenv new_decls ctx xs =
    let updatef = function
      | None -> Some (value, kind, args, tvenv)
      | t -> t in
    let next = StrMap.update n updatef new_decls in
    if next == new_decls then Error ["duplicate type definition " ^ n]
    else begin
      let foldf (_, qk) k = TArr (qk, k) in
      let kind = List.fold_right foldf args kind in
      let entry = (value, kind) in
      let tctors = StrMap.add n entry ctx.tctors in
      collect_names next { ctx with tctors } xs
    end in

  collect_names StrMap.empty ctx aliases

let visit_toplevel (ctx : context) (ast : Ast.ast_toplevel) =
  match ast with
    | Ast.TopAlias aliases ->
      let* (m, ctx) = visit_top_alias ctx aliases in
      Ok (AddTypes m, ctx)
    | Ast.TopDef defs ->
      let* (m, ctx) = visit_top_defs ctx defs in
      Ok (AddGlobl m, ctx)
    | Ast.TopTrait defs ->
      let* (m, ctx) = visit_top_trait ctx defs in
      Ok (AddGlobl m, ctx)
    | Ast.TopImpl defs ->
      let* (m, ctx) = visit_top_impl ctx defs in
      Ok (AddGlobl m, ctx)
    | Ast.TopExtern defs ->
      let* (m, ctx) = visit_top_externs ctx defs in
      Ok (AddExtern m, ctx)
    | Ast.TopExpr e ->
      let* (ast, ty, ctx) = visit_top_expr ctx e in
      Ok (EvalExpr (ast, ty), ctx)

let visit_prog (tctx : context) (ast : Ast.ast_toplevel list) =
  let rec loop acc tctx = function
    | [] -> Ok (List.rev acc, tctx)
    | x :: xs ->
      match visit_toplevel tctx x with
        | Error e -> Error e
        | Ok (m, tctx) -> loop (m :: acc) tctx xs in
  loop [] tctx ast