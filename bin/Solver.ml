open Printf
module T = Type

type cnst =
  | CnstEq of T.t * T.t
  | CnstFixed of T.NameSet.t * cnst list

let merge_cnst = function
  | [t] -> t
  | list -> CnstFixed (T.NameSet.empty, list)

let prune_cnst (cnst : cnst) : cnst =
  let rec prune_list acc = function
    | [] -> acc
    | CnstEq _ as x :: tl -> prune_list (x :: acc) tl
    | CnstFixed (s, ys) :: tl when T.NameSet.is_empty s ->
      prune_list acc (List.rev_append ys tl)
    | CnstFixed (s, ys) :: tl ->
      match prune_list [] ys with
        | [] -> prune_list acc tl
        | ys -> prune_list (CnstFixed (s, ys) :: acc) tl in
  prune_list [] [cnst] |> merge_cnst

type violation =
  | Mismatch of T.t * T.t
  | Cyclic of T.t * T.t

let explain : violation -> string = function
  | Mismatch (p, q) ->
    sprintf "Cannot unify unrelated types %s and %s"
      (T.to_string p) (T.to_string q)
  | Cyclic (p, q) ->
    sprintf "Cannot unify recursive types %s and %s"
      (T.to_string p) (T.to_string q)

let ( let* ) = Result.bind

let unify ?(fixed_tvars = T.NameSet.empty) (p : T.t) (q : T.t) =
  let can_mutate n id = not @@ T.NameSet.mem (n, id) fixed_tvars in
  let rec loop changed rem bad = function
    | [] -> if bad = [] then Ok (changed, rem) else Error bad
    | (p, q) :: tl ->
      let p = T.unwrap_shallow p in
      let q = T.unwrap_shallow q in
      match (p, q) with
        | (TRigid (n1, id1), TRigid (n2, id2)) when n1 = n2 && id1 = id2 ->
          loop changed rem bad tl

        | (TArr (f1, a1), TArr (f2, a2)) ->
          loop changed rem bad ((f1, f2) :: (a1, a2) :: tl)

        | (TTup xs, TTup ys) ->
          let rec collect_new acc = function
            | ([], []) -> loop changed rem bad acc
            | (x :: xs, y :: ys) -> collect_new ((x, y) :: acc) (xs, ys)
            | _ -> loop changed rem (Mismatch (p, q) :: bad) tl in
          collect_new tl (xs, ys)

        | (TVar (n1, id1, r1), TVar (n2, id2, r2)) ->
          if n1 = n2 && id1 = id2 then loop changed rem bad tl
          else if can_mutate n1 id1 then (r1 := Some q; loop changed rem bad tl)
          else if can_mutate n2 id2 then (r2 := Some p; loop changed rem bad tl)
          else loop changed (CnstEq (p, q) :: rem) bad tl

        | (TVar (n, id, r) as p, q) | (q, (TVar (n, id, r) as p)) ->
          if can_mutate n id then
            if T.contains_tvar (n, id) q then
              loop changed rem (Cyclic (p, q) :: bad) tl
            else (r := Some q; loop true rem bad tl)
          else loop changed (CnstEq (p, q) :: rem) bad tl

        | _ -> loop changed rem (Mismatch (p, q) :: bad) tl in
  loop false [] [] [p, q]

let rec dump_solver ppf : cnst -> unit = function
  | CnstEq (p, q) -> fprintf ppf "(%a ~ %a)" T.output p T.output q
  | CnstFixed (locked, sub) ->
    output_string ppf "[";
    T.NameSet.iter (fun (n, id) -> fprintf ppf " %s.%a" n Z.output id) locked;
    output_string ppf " ]{";
    List.iter (fprintf ppf " %a" dump_solver) sub;
    output_string ppf " }"

let solve (cnst : cnst list) =
  let rec visit fixed_tvars = function
    | CnstEq (p, q) -> unify ~fixed_tvars p q
    | CnstFixed (more, sub) ->
      let* (changed, acc) = visit_list (T.NameSet.union more fixed_tvars) sub in
      if acc = [] then Ok (changed, acc)
      else Ok (changed, [CnstFixed (more, sub)])

  and visit_list fixed_tvars list =
    let rec loop changed acc = function
      | [] -> Ok (changed, acc)
      | x :: xs ->
        let* (f, rem) = visit fixed_tvars x in
        loop (f || changed) (List.rev_append rem acc) xs in
    loop false [] list in

  let rec fixpoint cnst =
    let* (changed, cnst) = visit_list T.NameSet.empty cnst in
    if not changed || cnst = [] then Ok cnst
    else fixpoint cnst in

  fixpoint cnst
