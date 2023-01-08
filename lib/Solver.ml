open Printf
module T = Type
module V = VarInfo
module C = Core

type cnst =
  | CnstEq of V.Set.t * T.t * T.t
  | CnstSeq of cnst list
  | CnstPred of C.expr ref * T.pred
  | CnstImply of (C.expr * T.pred) list * cnst

let ( let* ) = Result.bind

let merge_cnst = function
  | [t] -> t
  | xs -> CnstSeq xs

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
  let rec loop changed rem xs =
    match T.decompose_pairs xs with
      | Error xs ->
        Error (List.rev_map (fun (p, q) -> Mismatch (p, q)) xs)
      | Ok [] -> Ok (changed, rem)
      | Ok xs ->
        let rec tail changed rem acc = function
          | [] -> loop changed rem acc
          | (p, q) :: xs ->
            let p = T.unwrap p in
            let q = T.unwrap q in
            match (p, q) with
              | (TQuant _, _) | (_, TQuant _) ->
                failwith "UNKNOWN QUANTIFIER DURING UNIFY STEP"
              | (TPred _, _) | (_, TPred _) ->
                failwith "UNKNOWN PREDICATE DURING UNIFY STEP"

              | (TVar (n1, r1), TVar (n2, r2)) ->
                if n1 = n2 then tail changed rem acc xs
                else begin
                  (* prefer getting rid of TVars that don't have names *)
                  let (n1, r1, n2, r2) =
                    if fst n1 = "" then (n1, r1, n2, r2)
                    else (n2, r2, n1, r1) in

                  if can_mutate n1 then
                    (r1 := Some (TVar (n2, r2)); tail changed rem acc xs)
                  else if can_mutate n2 then
                    (r2 := Some (TVar (n1, r1)); tail changed rem acc xs)
                  else
                    tail changed (CnstEq (fixed_tvars, p, q) :: rem) acc xs
                end

              | (TVar (n, r) as p, q) | (q, (TVar (n, r) as p)) ->
                if can_mutate n then
                  if T.contains_tvar n q then Error [Cyclic (p, q)]
                  else (r := Some q; tail true rem acc xs)
                else tail changed (CnstEq (fixed_tvars, p, q) :: rem) acc xs

              | _ -> tail changed rem ((p, q) :: acc) xs in
        tail changed rem [] xs in
  loop false [] [p, q]

let is_impl ((name, pattern)) t =
  let rec partition preds m id = function
    | T.TQuant (n, t) ->
      let id = Z.pred id in
      partition preds (V.Map.add n (T.TVar (("", id), ref None)) m) id t
    | T.TPred (p, t) -> partition (p :: preds) m id t
    | t -> (m, List.rev preds, t) in

  (* begin by "instantiating" the pattern *)
  let (rigid, deps, pat) = partition [] V.Map.empty Z.zero pattern in

  (* then check if it is the correct implementation by unification *)
  let rec loop pairs =
    match T.decompose_pairs pairs with
      | Error _ -> None
      | Ok [] ->
        (* if it matches, then yield the extra constraints (deps) *)
        Some (name, List.map (T.subst_pred ~rigid) deps)
      | Ok xs ->
        let rec tail tl = function
          | [] -> loop tl
          | (p, q) :: xs ->
            let p = T.unwrap p in
            let q = T.unwrap q in
            match (p, q) with
              | (TQuant _, _) | (_, TQuant _) ->
                failwith "UNKNOWN QUANTIFIER DURING UNIFY STEP"
              | (TPred _, _) | (_, TPred _) ->
                failwith "UNKNOWN PREDICATE DURING UNIFY STEP"

              (* in the following cases, we only allow the fresh weak types
               * generated here (all have negative id's) to be removed.
               *
               * this avoids the instances constraining the type (which is
               * the opposite of what we want) *)

              | (TVar (n1, r1), TVar (n2, r2)) ->
                if n1 = n2 then tail tl xs
                else begin
                  if Z.sign (snd n1) < 0 then
                    (r1 := Some (TVar (n2, r2)); tail tl xs)
                  else if Z.sign (snd n2) < 0 then
                    (r2 := Some (TVar (n1, r1)); tail tl xs)
                  else None (* not a candidate *)
                end

              | (TVar (n, r), q) | (q, TVar (n, r)) ->
                if Z.sign (snd n) < 0 then
                  (r := Some q; tail tl xs)
                else None (* not a candidate *)

              | _ -> tail ((p, q) :: tl) xs in
        tail [] xs in
  loop [T.subst ~rigid pat, t]

let solve (cnst : cnst list) =
  let rec visit ctx = function
    | CnstSeq xs ->
      let rec loop changed acc = function
        | [] -> begin
          match acc with
            | [x] -> Ok (changed, x)
            | _ -> Ok (changed, CnstSeq acc)
        end
        | x :: xs ->
          let* (f, rem) = visit ctx x in
          let changed = f || changed in
          match rem with
            | CnstSeq ys -> loop changed (List.rev_append ys acc) xs
            | rem -> loop changed (rem :: acc) xs in
      loop false [] xs

    | CnstEq (fixed_tvars, p, q) -> begin
      let* (changed, rem) = unify ~fixed_tvars p q in
      match rem with
        | [x] -> Ok (changed, x)
        | _ -> Ok (changed, CnstSeq rem)
    end

    | CnstImply ([], k) -> visit ctx k

    | CnstImply (new_ctx, k) -> begin
      let* (f, rem) = visit (new_ctx :: ctx) k in
      match rem with
        | CnstSeq [] -> Ok (f, CnstSeq [])
        | _ -> Ok (f, CnstImply (new_ctx, rem))
    end

    | CnstPred (r, PredTrait (trait, t)) -> begin
      let t = T.unwrap t in
      let Trait info = trait in
      match t with
        | TVar _ -> Ok (false, CnstPred (r, PredTrait (trait, t)))
        | _ ->
          let rec search acc = function
            | [] -> begin
              match acc with
                | [name, deps] ->
                  let rec emit_deps deps xs = function
                    | [] ->
                      let e = match deps with
                        | [] -> C.EVar (name, Z.zero)
                        | [x] -> C.EApp (C.EVar (name, Z.zero), x)
                        | _ ->
                          C.EApp (C.EVar (name, Z.zero), C.ETup (List.rev deps)) in
                      r := e;
                      visit ctx (CnstSeq xs)

                    | pred :: ts ->
                      let (tc, dep) = C.mk_empty_hole () in
                      let new_cnst = CnstPred (dep, pred) in
                      emit_deps (tc :: deps) (new_cnst :: xs) ts in
                  emit_deps [] [] deps

                | [] ->
                  (* search the context for evidence *)
                  let rec search_ctx = function
                    | [] -> Ok (false, CnstPred (r, PredTrait (trait, t)))
                    | x :: xs ->
                      let predf (_, T.PredTrait (q, evidence)) =
                        q == trait && T.decompose evidence t = Ok [] in
                      match List.find_opt predf x with
                        | None -> search_ctx xs
                        | Some (e, _) -> r := e; Ok (false, CnstSeq []) in
                  search_ctx ctx
                | _ ->
                  (* ambiguous match: report it later *)
                  Ok (false, CnstPred (r, PredTrait (trait, t)))
            end
            | trait_entry :: xs ->
              match is_impl trait_entry t with
                | None -> search acc xs
                | Some p -> search (p :: acc) xs in
          search [] info.allowed
    end in

  let rec fixpoint cnst =
    let* (changed, cnst) = visit [] cnst in
    match (cnst, changed) with
      | (CnstSeq [], _) -> Ok []
      | (CnstSeq r, false) -> Ok r
      | (r, false) -> Ok [r]
      | (_, true) -> fixpoint cnst in

  fixpoint (CnstSeq cnst)

let rec explain_remaining : cnst -> string = function
  | CnstEq (s, (T.TVar (n, _) as p), q) when V.Set.mem n s ->
    sprintf "Unification of types %s with %s would result in loss of generality"
      (T.to_string p) (T.to_string q)
  | CnstEq (s, q, (T.TVar (n, _) as p)) when V.Set.mem n s->
    sprintf "Unification of types %s with %s would result in loss of generality"
      (T.to_string p) (T.to_string q)
  | CnstPred (_, p) ->
    sprintf "Not sure how to resolve %s" (T.pred_to_string p)
  | CnstImply (_, q) -> explain_remaining q
  | _ -> "Impossible type unification"