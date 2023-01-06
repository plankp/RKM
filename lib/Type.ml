open Printf
module V = VarInfo

type t =
(* a weak unification variable *)
  | TVar of tvinfo

(* a rigid type variable: what TQuants and ETyLam uses *)
  | TRigid of V.t

(* common monotypes *)
  | TChr
  | TStr
  | TInt
  | TArr of t * t
  | TTup of t list
  | TCons of tctor * t list

(* for traits and other future constraints *)
  | TPred of pred * t

(* for higher kinded stuff *)
  | TKind
  | TQuant of V.t * t (* quantized over rigid variables *)
  | TApp of t * t

and tvinfo = V.t * t option ref

and pred =
  | PredTraitEq of t

and tctor =
  | TCtorArr
  | TCtorVar of variant

and variant = {
  name : string;
  quants : V.t list;

  (*
   * only stores the arguments. e.g., for list
   *        Surface type        | Stored as
   * []   : \a. [a]             | []
   * (::) : \a. a -> [a] -> [a] | [a, #list a]
   *)
  cases : (string, t list) Hashtbl.t;
}

(* data Bool = True | False *)
let varBool : variant = {
  name = "Bool";
  quants = [];
  cases = Hashtbl.create 2;
}

let tyBool = TCons (TCtorVar varBool, [])
let () =
  Hashtbl.replace varBool.cases "True" [];
  Hashtbl.replace varBool.cases "False" []

(* data [a] = [] | a :: [a] *)
let varList : variant = {
  name = "[]";
  quants = [("a", Z.zero)];
  cases = Hashtbl.create 2;
}

let tyList t = TCons (TCtorVar varList, [t])
let () =
  Hashtbl.replace varList.cases "[]" [];
  Hashtbl.replace varList.cases "(::)" [TRigid ("a", Z.zero); tyList (TRigid ("a", Z.zero))]

(* data ref a = ref a *)
let varRef : variant = {
  name = "ref";
  quants = [("a", Z.zero)];
  cases = Hashtbl.create 1;
}

let tyRef t = TCons (TCtorVar varRef, [t])
let () =
  Hashtbl.replace varRef.cases "ref" [TRigid ("a", Z.zero)]

let rec unwrap : t -> t = function
  | TVar (_, ({ contents = Some t } as r)) ->
    let t = unwrap t in r := Some t; t
  | t -> t

let rec output ppf = function
  | TVar (_, { contents = Some _ }) as t -> output ppf (unwrap t)
  | TVar (n, _) | TRigid n -> V.output ppf n
  | TChr -> output_string ppf "Char"
  | TStr -> output_string ppf "String"
  | TInt -> output_string ppf "Int"
  | TKind -> output_string ppf "*"
  | TArr (p, q) ->
    fprintf ppf "%a -> %a" output (check_arr_prec p) output q
  | TApp (p, q) ->
    fprintf ppf "%a %a" output p output (check_app_prec q)
  | TTup [] -> output_string ppf "()"
  | TTup (x :: xs) ->
    fprintf ppf "(%a" output x;
    List.iter (fprintf ppf ", %a" output) xs;
    output_string ppf ")"
  | TCons (TCtorVar k, [x]) when k == varList -> fprintf ppf "[%a]" output x
  | TCons (k, []) -> output_string ppf (tctor_to_string k)
  | TCons (k, x :: xs) ->
    fprintf ppf "%s %a" (tctor_to_string k) output (check_app_prec x);
    List.iter (fun x -> fprintf ppf " %a" output (check_app_prec x)) xs
  | TPred (p, t) ->
    fprintf ppf "%a => %a" output_pred p output t
  | TQuant (n, t) ->
    fprintf ppf "(\\%a. %a)" V.output n output t

and to_string = function
  | TVar (_, { contents = Some _ }) as t -> to_string (unwrap t)
  | TVar (n, _) | TRigid n -> V.to_string n
  | TChr -> "Char"
  | TStr -> "String"
  | TInt -> "Int"
  | TKind -> "*"
  | TArr (p, q) ->
    sprintf "%s -> %s" (to_string (check_arr_prec p)) (to_string q)
  | TApp (p, q) ->
    sprintf "%s %s" (to_string p) (to_string (check_app_prec q))
  | TTup [] -> "()"
  | TTup (x :: xs) ->
    let buf = Buffer.create 32 in
    Buffer.add_string buf "(";
    Buffer.add_string buf (to_string (check_app_prec x));
    List.iter (fun x -> bprintf buf ", %s" (to_string (check_app_prec x))) xs;
    Buffer.add_string buf ")";
    Buffer.contents buf
  | TCons (TCtorVar k, [x]) when k == varList -> sprintf "[%s]" (to_string x)
  | TCons (k, []) -> tctor_to_string k
  | TCons (k, x :: xs) ->
    let buf = Buffer.create 32 in
    bprintf buf "%s %s" (tctor_to_string k) (to_string (check_app_prec x));
    List.iter (fun x -> bprintf buf " %s" (to_string (check_app_prec x))) xs;
    Buffer.contents buf
  | TPred (p, t) ->
    sprintf "%s => %s" (pred_to_string p) (to_string t)
  | TQuant (n, t) ->
    sprintf "(\\%s. %s)" (V.to_string n) (to_string t)

and tctor_to_string = function
  | TCtorArr -> "(->)"
  | TCtorVar k -> k.name

and output_pred ppf = function
  | PredTraitEq t ->
    fprintf ppf "Eq %a" output (check_app_prec t)

and pred_to_string = function
  | PredTraitEq t ->
    sprintf "Eq %s" (to_string (check_app_prec t))

and check_app_prec = function
  | TVar (_, { contents = Some _ }) as t -> check_app_prec (unwrap t)
  | TApp _ | TCons (_, _ :: _) as q -> TTup [q]
  | q -> q

and check_arr_prec = function
  | TVar (_, { contents = Some _ }) as t -> check_arr_prec (unwrap t)
  | TArr _ | TPred _ as q -> TTup [q]
  | q -> q

let rec equiv (p : t) (q : t) : bool =
  let rec loop = function
    | [] -> true
    | (p, q) :: tl ->
      let p = unwrap p in
      let q = unwrap q in
      let rec collect_new acc = function
        | ([], []) -> loop acc
        | (x :: xs, y :: ys) -> collect_new ((x, y) :: acc) (xs, ys)
        | _ -> false in
      match (p, q) with
        | (TQuant _, _) | (_, TQuant _) ->
          failwith "UNKNOWN QUANTIFIER FOR EQUIV"
        | (TPred _, _) | (_, TPred _) ->
          failwith "UNKNOWN PREDICATE FOR EQUIV"

        | (TVar (p, _), TVar (q, _)) | (TRigid p, TRigid q) ->
          if p = q then loop tl else false

        | (TChr, TChr) | (TStr, TStr) | (TInt, TInt) | (TKind, TKind) ->
          loop tl

        | (TArr (f1, a1), TArr (f2, a2)) | (TApp (f1, a1), TApp (f2, a2)) ->
          loop ((f1, f2) :: (a1, a2) :: tl)

        | (TTup xs, TTup ys) | (TCons (TCtorArr, xs), TCons (TCtorArr, ys)) ->
          collect_new tl (xs, ys)

        | (TCons (TCtorVar k1, xs), TCons (TCtorVar k2, ys)) when k1 == k2 ->
          collect_new tl (xs, ys)

        | _ -> false in
  loop [p, q]

and pred_equiv (p : pred) (q : pred) : bool =
  match (p, q) with
    | (PredTraitEq p, PredTraitEq q) -> equiv p q

let rec subst ?(rigid = V.Map.empty) ?(weak = V.Map.empty) = function
  | TChr | TStr | TInt | TKind as t -> t
  | TVar (_, { contents = Some _ }) as t -> subst ~rigid ~weak (unwrap t)
  | TVar (n, _) as t -> begin
    match V.Map.find_opt n weak with
      | Some t -> subst ~rigid ~weak t
      | None -> t
  end
  | TRigid n as t -> begin
    match V.Map.find_opt n rigid with
      | Some t -> subst ~rigid ~weak t
      | None -> t
  end
  | TArr (p, q) -> TArr (subst ~rigid ~weak p, subst ~rigid ~weak q)
  | TTup xs -> TTup (List.map (subst ~rigid ~weak) xs)
  | TCons (k, xs) -> TCons (k, List.map (subst ~rigid ~weak) xs)
  | TApp (p, q) -> TApp (subst ~rigid ~weak p, subst ~rigid ~weak q)
  | TPred (PredTraitEq p, q) ->
    TPred (PredTraitEq (subst ~weak ~rigid p), subst ~weak ~rigid q)
  | TQuant (n, t) -> TQuant (n, subst ~weak ~rigid:(V.Map.remove n rigid) t)

let rec eval (map : t V.Map.t) (env : V.Set.t) : t -> t = function
  | TRigid n as t -> V.Map.find_opt n map |> Option.value ~default:t
  | TVar (_, { contents = Some _ }) as t -> eval map env (unwrap t)
  | TVar _ | TChr | TStr | TInt | TKind as t -> t
  | TArr (p, q) -> TArr (eval map env p, eval map env q)
  | TTup xs -> TTup (List.map (eval map env) xs)
  | TCons (k, xs) -> TCons (k, List.map (eval map env) xs)
  | TApp (p, q) -> begin
    match (eval map env p, eval map env q) with
      | (TCons (TCtorArr, [p]), q) -> TArr (p, q)
      | (TCons (k, xs), q) -> TCons (k, xs @ [q])
      | (TQuant (n, t), q) -> eval (V.Map.add n q map) env t
      | (p, q) -> TApp (p, q)
  end
  | TPred (PredTraitEq p, q) ->
    TPred (PredTraitEq (eval map env p), eval map env q)
  | TQuant (n, t) ->
    let (n, map, env) = V.def_var (fun n -> TRigid n) n map env in
    TQuant (n, eval map env t)

let normalize (t : t) =
  eval V.Map.empty V.Set.empty t

let inst_variant (v : variant) (args : t list) =
  let foldf m q arg = V.Map.add q arg m in
  let env = List.fold_left2 foldf V.Map.empty v.quants args in
  let foldf k args acc = (k, List.map (eval env V.Set.empty) args) :: acc in
  Hashtbl.fold foldf v.cases []

let inst_case (v : variant) (k : string) (targs : t list) =
  match Hashtbl.find_opt v.cases k with
    | None -> None
    | Some args ->
      let foldf m q arg = V.Map.add q arg m in
      let env = List.fold_left2 foldf V.Map.empty v.quants targs in
      Some (List.map (eval env V.Set.empty) args)

let rec contains_quant = function
  | TQuant _ -> true
  | TVar (_, { contents = Some _ }) as t -> contains_quant (unwrap t)
  | TVar _ | TRigid _ | TChr | TStr | TInt | TKind -> false
  | TArr (p, q) | TApp (p, q) -> contains_quant p || contains_quant q
  | TTup xs | TCons (_, xs) -> List.exists contains_quant xs
  | TPred (PredTraitEq p, q) -> contains_quant p || contains_quant q

let rec contains_tvar n = function
  | TVar (_, { contents = Some _ }) as t -> contains_tvar n (unwrap t)
  | TVar (m, _) -> n = m
  | TRigid _ | TChr | TStr | TInt | TKind -> false
  | TArr (p, q) | TApp (p, q) ->
    contains_tvar n p || contains_tvar n q
  | TTup xs | TCons (_, xs) ->
    List.exists (contains_tvar n) xs
  | TPred (PredTraitEq p, q) ->
    contains_tvar n p || contains_tvar n q
  | TQuant (_, t) -> contains_tvar n t

let fold_free_tvars (f : tvinfo -> 'a -> 'a) (t : t) (i : 'a) : 'a =
  let rec loop i = function
    | [] -> i
    | TVar (_, { contents = Some _ }) as t :: xs -> loop i (unwrap t :: xs)
    | TVar tvinfo :: xs -> loop (f tvinfo i) xs
    | (TRigid _ | TChr | TStr | TInt | TKind) :: xs -> loop i xs
    | (TArr (p, q) | TApp (p, q)) :: xs -> loop i (p :: q :: xs)
    | (TTup ys | TCons (_, ys)) :: xs -> loop (loop i ys) xs
    | TPred (PredTraitEq p, q) :: xs -> loop i (p :: q :: xs)
    | TQuant (_, t) :: xs -> loop i (t :: xs) in
  loop i [t]

let free_tvars ?(acc = V.Set.empty) (t : t) : V.Set.t =
  fold_free_tvars (fun (n, _) acc -> V.Set.add n acc) t acc

let collect_free_tvars (t : t) : tvinfo list =
  let foldf (n, r) (fs, set) =
    if V.Set.mem n set then (fs, set)
    else ((n, r) :: fs, V.Set.add n set) in
  fold_free_tvars foldf t ([], V.Set.empty) |> fst |> List.rev

let dangerous_vars ?(acc = V.Set.empty) (t : t) : V.Set.t =
  let rec loop acc = function
    | [] -> acc
    | TVar (_, { contents = Some _ }) as t :: xs -> loop acc (unwrap t :: xs)
    | (TVar _ | TRigid _ | TChr | TStr | TInt | TKind) :: xs -> loop acc xs
    | (TCons (TCtorVar k, _) as t) :: xs when k == varRef ->
      loop (free_tvars ~acc t) xs
    | (TCons (TCtorVar k, ys)) :: xs when k == varList ->
      loop acc (List.rev_append ys xs)
    | TArr (p, q) :: xs -> loop (free_tvars ~acc p) (q :: xs)
    | TTup ys :: xs -> loop acc (List.rev_append ys xs)
    | TQuant (_, t) :: xs -> loop acc (t :: xs)
    | t :: xs ->
      (* assume the worst for everything else *)
      loop (free_tvars ~acc t) xs in
  loop acc [t]
