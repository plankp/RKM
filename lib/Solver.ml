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
        | (TPred _, _) | (_, TPred _) ->
          failwith "UNKNOWN PREDICATE DURING UNIFY STEP"

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
  let rec search_ctx p = function
    | [] -> None
    | ctx :: xs ->
      match List.find_opt (fun (_, impl) -> T.pred_equiv p impl) ctx with
        | None -> search_ctx p xs
        | Some (e, _) -> Some e in

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

    | CnstPred (r, p) -> begin
      match p with
        | PredTraitEq t ->
          match T.unwrap t with
            | TInt | TChr | TStr as t ->
              r := C.EVar (sprintf "@$Impl[Eq %s]" (T.to_string t), Z.zero);
              Ok (false, CnstSeq [])

            | TCons (TCtorVar k, []) as t when k == T.varBool ->
              r := C.EVar (sprintf "@$Impl[Eq %s]" (T.to_string t), Z.zero);
              Ok (false, CnstSeq [])

            | TCons (TCtorVar k, [elt]) when k == T.varList || k == T.varRef ->
              let (tc, dep) = C.mk_empty_hole () in
              r := C.EApp (C.EVar ("@$Impl[Eq List a]", Z.zero), tc);
              visit ctx (CnstPred (dep, PredTraitEq elt))

            | TTup [] ->
              r := C.EVar (sprintf "@$Impl[Eq ()]", Z.zero);
              Ok (false, CnstSeq [])

            | TTup ys ->
              let buf = Buffer.create 32 in
              Buffer.add_string buf "@$Impl[Eq (";
              let rec emit_deps deps xs = function
                | [] ->
                  Buffer.add_string buf ")]";
                  r := C.EApp (C.EVar (Buffer.contents buf, Z.zero), C.ETup (List.rev deps));
                  visit ctx (CnstSeq xs)
                | t :: ts ->
                  let (tc, dep) = C.mk_empty_hole () in
                  Buffer.add_char buf ',';
                  emit_deps (tc :: deps) (CnstPred (dep, PredTraitEq t) :: xs) ts in
              emit_deps [] [] ys

            | t ->
              match search_ctx p ctx with
                | Some e -> r := e; Ok (false, CnstSeq [])
                | None -> Ok (false, CnstPred (r, PredTraitEq t))
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