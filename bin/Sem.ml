open Ast
module C = Core
module T = Type
module S = Solver
module M = Map.Make (String)

type context = {
  venv : T.t M.t list;
  id : Z.t;

  fixed_tvars : T.NameSet.t;
}

let ( let* ) = Result.bind

let init_context : context = {
  venv = [];
  id = Z.zero;
  fixed_tvars = T.NameSet.empty;
}

let mk_name (ctx : context) (name : string) : (T.Name.t * context) =
  let id = Z.succ ctx.id in
  ((name, ctx.id), { ctx with id })

let mk_tvar (ctx : context) (name : string) : (T.t * context) =
  let id = Z.succ ctx.id in
  (T.TVar (name, ctx.id, ref None), { ctx with id })

let inst (ctx : context) (t : T.t) : (T.t list * T.t * context) =
  let rec loop qs m ctx = function
    | T.TPoly (n, id, t) ->
      let (new_tv, ctx) = mk_tvar ctx n in
      loop (new_tv :: qs) (T.NameMap.add (n, id) new_tv m) ctx t
    | t -> (List.rev qs, T.subst ~rigid:m t, ctx) in
  loop [] T.NameMap.empty ctx t

let gen (ctx : context) (qs : T.t list) (t : T.t) =
  let foldf (acc, map, ctx) t =
    let (n, id) = T.get_name t in
    let ((rn, rid), ctx) = mk_name ctx n in
    let new_rigid = T.TRigid (rn, rid) in
    ((rn, rid) :: acc, T.NameMap.add (n, id) new_rigid map, ctx) in
  let (qs, m, ctx) = List.fold_left foldf ([], T.NameMap.empty, ctx) qs in
  (qs, T.subst ~weak:m t, m, ctx)

let free_tvars_ctx (ctx : context) =
  let rec loop (set, acc) = function
    | [] -> (set, acc)
    | x :: xs ->
      let foldf _ t acc = T.free_tvars ~acc t in
      loop (M.fold foldf x (set, acc)) xs in
  loop (T.NameSet.empty, []) ctx.venv

let rec infer (ctx : context) (expr : expr) =
  match expr with
    | EVar name ->
      let rec loop = function
        | [] -> Error ["undefined variable " ^ name]
        | x :: xs ->
          match M.find_opt name x with
            | None -> loop xs
            | Some p ->
              let e = C.EVar (name, Z.zero, p) in
              let (qs, t, ctx) = inst ctx p in
              let e = List.fold_left (fun e q -> C.EApp (e, C.EType q)) e qs in
              Ok (e, t, S.merge_cnst [], ctx) in
      loop ctx.venv

    | EApp (e1, e2) ->
      let* (e1, t1, f1, ctx) = infer ctx e1 in
      let* (e2, t2, f2, ctx) = infer ctx e2 in
      let (a, ctx) = mk_tvar ctx "" in
      Ok (C.EApp (e1, e2), a, S.merge_cnst [f1; f2; S.CnstEq (t1, T.TArr (t2, a))], ctx)

    | EAbs (x, e) ->
      let (a, ctx) = mk_tvar ctx "" in
      let ctx = { ctx with venv = M.singleton x a :: ctx.venv } in
      let* (e, t, f, ctx) = infer ctx e in
      let ctx = { ctx with venv = List.tl ctx.venv } in
      Ok (C.ELam (x, Z.zero, a, e), T.TArr (a, t), f, ctx)

    | ETup xs ->
      let rec loop elts types cnsts ctx = function
        | [] ->
          Ok (C.ETup (List.rev elts), T.TTup (List.rev types), S.merge_cnst cnsts, ctx)
        | x :: xs ->
          let* (e, t, f, ctx) = infer ctx x in
          loop (e :: elts) (t :: types) (f :: cnsts) ctx xs in
      loop [] [] [] ctx xs

    | ELet (g, e1, e2) -> begin
      let (a, ctx) = mk_tvar ctx "" in
      let ctx = { ctx with venv = M.singleton g a :: ctx.venv } in
      let* (e1, t, f1, ctx) = infer ctx e1 in
      match S.unify ~fixed_tvars:ctx.fixed_tvars t a with
        | Error e -> Error (List.rev_map S.explain e)
        | Ok (_, f3) ->
          (* only generalize when there are no pending constraints *)
          match S.prune_cnst (S.merge_cnst [f1; S.merge_cnst f3]) with
            | S.CnstFixed (_, []) ->
              (* there are no pending constraints: generalize *)
              let ctx = { ctx with venv = List.tl ctx.venv } in
              let (_, qs) = T.free_tvars t in
              let (monos, _) = free_tvars_ctx ctx in
              let filterf t = not (T.NameSet.mem (T.get_name t) monos) in
              let qs = List.filter filterf qs in
              let (qs, t, m, ctx) = gen ctx qs t in
              let t = List.fold_right (fun (n, id) t -> T.TPoly (n, id, t)) qs t in
              let ctx = { ctx with venv = M.singleton g t :: ctx.venv } in
              let* (e2, v, f2, ctx) = infer ctx e2 in
              let ctx = { ctx with venv = List.tl ctx.venv } in
              let e1 = List.fold_right (fun (n, id) e -> C.ETyLam (n, id, e)) qs e1 in
              Ok (C.ELet (g, Z.zero, t, C.subst_type ~weak:m e1, e2), v, f2, ctx)
            | f1 ->
              (* there are pending constraints: don't generalize *)
              let* (e2, v, f2, ctx) = infer ctx e2 in
              let ctx = { ctx with venv = List.tl ctx.venv } in
              Ok (C.ELet (g, Z.zero, a, e1, e2), v, S.merge_cnst [f1; f2; S.CnstEq (t, a)], ctx)
    end

    | ELetA (g, ta, e1, e2) ->
      let fuv = free_tvars_ctx ctx in
      let old_fixed_tvars = ctx.fixed_tvars in

      let ctx = { ctx with
        fixed_tvars = fst fuv;
        venv = M.singleton g ta :: ctx.venv } in
      let* (e1, t, f1, ctx) = infer ctx e1 in
      let* (e2, v, f2, ctx) = infer ctx e2 in
      let ctx = { ctx with
        fixed_tvars = old_fixed_tvars;
        venv = List.tl ctx.venv } in
      let (a, ta) = T.unpeel_poly ta in
      let e = List.fold_left (fun e (n, id) -> C.ETyLam (n, id, e)) e1 a in
      let e = C.ELet (g, Z.zero, ta, e, e2) in
      Ok (e, v, S.merge_cnst [f2; S.CnstFixed (fst fuv, [f1; S.CnstEq (ta, t)])], ctx)