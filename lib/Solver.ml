open Printf
module T = Type
module V = VarInfo

type cnst =
  | CnstEq of V.Set.t * T.t * T.t
  | CnstSeq of cnst list

let ( let* ) = Result.bind

let merge_cnst = function
  | [t] -> t
  | xs -> CnstSeq xs

let init_last head tail =
  let rec loop acc head = function
    | [] -> (List.rev acc, head)
    | x :: xs -> loop (head :: acc) x xs in
  loop [] head tail

type bad_unify =
  | Mismatch of T.t * T.t
  | Cyclic of T.t * T.t

let explain : bad_unify -> string = function
  | Cyclic (v, q) ->
    sprintf "Cannot unify recursive types %s and %s" (T.to_string v) (T.to_string q)
  | Mismatch (p, q) ->
    sprintf "Cannot unify unrelated types %s and %s" (T.to_string p) (T.to_string q)

let unify ?(fixed_tvars = V.Set.empty) (p : T.t) (q : T.t) =
  let can_mutate n = not @@ V.Set.mem n fixed_tvars in
  let rec loop changed rem bad = function
    | [] -> if bad = [] then Ok (changed, rem) else Error bad
    | (p, q) :: tl ->
      let p = T.unwrap p in
      let q = T.unwrap q in
      let rec collect_new acc = function
        | ([], []) -> loop changed rem bad acc
        | (x :: xs, y :: ys) -> collect_new ((x, y) :: acc) (xs, ys)
        | _ -> loop changed rem (Mismatch (p, q) :: bad) tl in
      match (p, q) with
        | (TQuant _, _) | (_, TQuant _) ->
          failwith "UNKNOWN QUANTIFIER DURING UNIFY STEP"

        | (TRigid p, TRigid q) when p = q ->
          loop changed rem bad tl
        | (TChr, TChr) | (TStr, TStr) | (TInt, TInt)
        | (TKind, TKind) ->
          loop changed rem bad tl

        | (TArr (f1, a1), TArr (f2, a2))
        | (TApp (f1, a1), TApp (f2, a2)) ->
          loop changed rem bad ((f1, f2) :: (a1, a2) :: tl)

        | (TTup xs, TTup ys)
        | (TCons (TCtorArr, xs), TCons (TCtorArr, ys)) ->
          collect_new tl (xs, ys)

        | (TCons (TCtorVar k1, xs), TCons (TCtorVar k2, ys)) when k1 == k2 ->
          collect_new tl (xs, ys)

        | (TCons (k, x :: xs), TApp (f, a))
        | (TApp (f, a), TCons (k, x :: xs)) ->
          let (init, last) = init_last x xs in
          loop changed rem bad ((TCons (k, init), f) :: (last, a) :: tl)

        | (TArr (p, q), TApp (f, a))
        | (TApp (f, a), TArr (p, q)) ->
          loop changed rem bad ((TCons (TCtorArr, [p]), f) :: (q, a) :: tl)

        | (TVar (n1, r1), TVar (n2, r2)) ->
          if n1 = n2 then loop changed rem bad tl
          else begin
            (* prefer getting rid of tvars that don't have names *)
            let (n1, r1, n2, r2) =
              if fst n1 = "" then (n1, r1, n2, r2)
              else (n2, r2, n1, r1) in

            if can_mutate n1 then
              (r1 := Some (TVar (n2, r2)); loop changed rem bad tl)
            else if can_mutate n2 then
              (r2 := Some (TVar (n1, r1)); loop changed rem bad tl)
            else loop changed (CnstEq (fixed_tvars, p, q) :: rem) bad tl
          end

        | (TVar (n, r) as p, q) | (q, (TVar (n, r) as p)) ->
          if can_mutate n then
            if T.contains_tvar n q then
              loop changed rem (Cyclic (p, q) :: bad) tl
            else (r := Some q; loop true rem bad tl)
          else loop changed (CnstEq (fixed_tvars, p, q) :: rem) bad tl

        | _ -> loop changed rem (Mismatch (p, q) :: bad) tl in
  loop false [] [] [p, q]

let solve (cnst : cnst list) =
  let visit_list list =
    let rec loop changed acc = function
      | [] -> Ok (changed, acc)
      | CnstSeq ys :: xs ->
        let* (changed, acc) = loop changed acc ys in
        loop changed acc xs
      | CnstEq (fixed_tvars, p, q) :: xs ->
        let* (f, rem) = unify ~fixed_tvars p q in
        loop (f || changed) (List.rev_append rem acc) xs in
    loop false [] list in

  let rec fixpoint cnst =
    let* (changed, cnst) = visit_list cnst in
    if not changed || cnst = [] then Ok cnst
    else fixpoint cnst in

  fixpoint cnst

let explain_remaining : cnst -> string = function
  | CnstEq (s, (T.TVar (n, _) as p), q) when V.Set.mem n s ->
    sprintf "Unification of types %s with %s would result in loss of generality"
      (T.to_string p) (T.to_string q)
  | CnstEq (s, q, (T.TVar (n, _) as p)) when V.Set.mem n s->
    sprintf "Unification of types %s with %s would result in loss of generality"
      (T.to_string p) (T.to_string q)
  | _ -> "Impossible type unification"