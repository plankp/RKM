module StrMap = Map.Make (String)

type tctx = {
  id : Int64.t;
  ctors : (Type.t * Type.t) StrMap.t;
  env : (Type.t * Type.t) StrMap.t list;
  rules : (Type.t * Type.t) list;
}

let map_of_list (list : (string * 'a) list) =
  list |> List.to_seq |> StrMap.of_seq

let core_tctx : tctx = {
  id = 0L;
  ctors = map_of_list ([
    "(->)", (TCons (TCtorArr, []), TArr (TKind, TArr (TKind, TKind)));
    "Char", (TChr, TKind);
    "String", (TStr, TKind);
    "Int", (TInt, TKind);
  ] : (string * (Type.t * Type.t)) list);
  env = [];
  rules = []
}

let visit_ast_type (allow_ign : bool) (tctx : tctx) (ast : Ast.ast_typ) =
  let rec visit tctx = function
    | Ast.TypeIgn ->
      if allow_ign then
        let ty = Type.TVar ("_", tctx.id)
        and kind = Type.TVar ("", tctx.id)
        and tctx = { tctx with id = Int64.succ tctx.id } in
        (Ok (ty, kind), tctx)
      else (Error ["unnamed type not allowed in this context"], tctx)
    | Ast.TypeVar n -> begin
      let rec loop = function
        | [] -> (Error ["unknown type variable named " ^ n], tctx)
        | x :: xs ->
          match StrMap.find_opt n x with
            | None -> loop xs
            | Some (ty, kind) -> (Ok (ty, kind), tctx) in
      loop tctx.env
    end
    | Ast.TypeCtor n -> begin
      match StrMap.find_opt n tctx.ctors with
        | None -> (Error ["unknown type constructor named " ^ n], tctx)
        | Some (ty, kind) ->
          let rec loop tctx map = function
            | Type.TQuant (q, k) ->
              let kind = Type.TVar ("", tctx.id)
              and tctx = { tctx with id = Int64.succ tctx.id } in
              loop tctx (VarInfo.Map.add q kind map) k
            | kind ->
              let kind =
                if VarInfo.Map.is_empty map then kind
                else Type.eval map VarInfo.Set.empty kind in
              (Ok (ty, kind), tctx) in
          loop tctx VarInfo.Map.empty kind
    end
    | Ast.TypeApp (p, q) -> begin
      let (p, tctx) = visit tctx p in
      let (q, tctx) = visit tctx q in
      match (p, q) with
        | (Error p, Error q) -> (Error (p @ q), tctx)
        | (Error p, _) | (_, Error p) -> (Error p, tctx)
        | (Ok (p, pkind), Ok (q, qkind)) ->
          let kind = Type.TVar ("", tctx.id)
          and tctx = { tctx with id = Int64.succ tctx.id } in
          let rules = (pkind, Type.TArr (qkind, kind)) :: tctx.rules in
          (Ok (Type.TApp (p, q), kind), { tctx with rules })
    end
    | Ast.TypeTup xs -> begin
      let rec loop acc tctx = function
        | [] ->
          let mapf xs = (Type.TTup (List.rev xs), Type.TKind) in
          (Result.map mapf acc, tctx)
        | x :: xs ->
          let (x, tctx) = visit tctx x in
          match (acc, x) with
            | (Error p, Error q) -> loop (Error (p @ q)) tctx xs
            | (Error p, _) | (_, Error p) -> loop (Error p) tctx xs
            | (Ok acc, Ok (x, xkind)) ->
              let rules = (xkind, Type.TKind) :: tctx.rules in
              loop (Ok (x :: acc)) { tctx with rules } xs in
      loop (Ok []) tctx xs
    end in

  match visit tctx ast with
    | (Ok (ty, kind), tctx) ->
      let ty = Type.normalize ty in
      if Type.contains_quant ty then (Error ["unsaturated type aliases are not allowed"], tctx)
      else (Ok (ty, kind), tctx)
    | t -> t

let visit_alias (tctx : tctx) (ast : Ast.ast_alias) =
  let (n, args, t) = ast in
  let rec tail tctx map acc errors = function
    | [] ->
      if errors = [] then begin
        let old_env = tctx.env in
        let old_rules = tctx.rules in
        match visit_ast_type false { tctx with env = [map]; rules = [] } t with
          | (Error e, _) -> Error e
          | (Ok (t, k), tctx) ->
            match Type.unify VarInfo.Map.empty tctx.rules with
              | (_, (_ :: _ as errors)) -> Error (List.map Type.explain errors)
              | (subst, []) ->
                let (k, subst) = Type.expand subst k in
                let foldf (t, k, subst) (q, qk) =
                  let (qk, subst) = Type.expand subst qk in
                  (Type.TQuant (q, t), Type.TArr (qk, k), subst) in
                let (t, k, _) = List.fold_left foldf (t, k, subst) acc in
                let (quants, k) = Type.gen VarInfo.Set.empty k in
                let k = List.fold_right (fun q k -> Type.TQuant (q, k)) quants k in
                Ok (n, t, k, { tctx with env = old_env; rules = old_rules })
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

let visit_toplevel (tctx : tctx) (ast : Ast.ast_toplevel) =
  match ast with
    | Ast.TopAlias aliases ->
      let rec loop tctx map errors = function
        | [] ->
          if errors = [] then
            let ctors = merge_map tctx.ctors map in
            Ok { tctx with ctors }
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
    | _ -> Error ["NOT IMPLEMENTED YET"]

let visit_prog (tctx : tctx) (ast : Ast.ast_toplevel list) =
  let rec loop tctx = function
    | [] -> Ok tctx
    | x :: xs ->
      match visit_toplevel tctx x with
        | Error e -> Error e
        | Ok tctx -> loop tctx xs in
  loop tctx ast