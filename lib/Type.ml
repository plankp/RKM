open Printf
module V = VarInfo

type t =
  | TVar of V.t       (* a (weak) type variable *)
  | TRigid of V.t     (* a rigid type variable: only unifies with itself *)
  | TChr
  | TStr
  | TInt
  | TArr of t * t
  | TTup of t list
  | TKind
  | TCons of tctor * t list
  | TQuant of V.t * t (* quantized over rigid variables *)
  | TApp of t * t

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
  quants = [("a", 0L)];
  cases = Hashtbl.create 2;
}

let tyList t = TCons (TCtorVar varList, [t])
let () =
  Hashtbl.replace varList.cases "[]" [];
  Hashtbl.replace varList.cases "(::)" [TRigid ("a", 0L); tyList (TRigid ("a", 0L))]

let rec output ppf = function
  | TVar n | TRigid n -> V.output ppf n
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
    List.iter (fun x -> fprintf ppf ", %a" output (check_app_prec x)) xs
  | TQuant (n, t) ->
    fprintf ppf "(\\%a. %a)" V.output n output t

and to_string = function
  | TVar n | TRigid n -> V.to_string n
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
    List.iter (fun x -> bprintf buf ", %s" (to_string (check_app_prec x))) xs;
    Buffer.contents buf
  | TQuant (n, t) ->
    sprintf "(\\%s. %s)" (V.to_string n) (to_string t)

and tctor_to_string = function
  | TCtorArr -> "(->)"
  | TCtorVar k -> k.name

and check_app_prec = function
  | TApp _ | TCons (_, _ :: _) as q -> TTup [q]
  | q -> q

and check_arr_prec = function
  | TArr _ as q -> TTup [q]
  | q -> q

let is_general_enough (a : t) (b : t) =
  let rec unpeel_quants = function
    | TQuant (_, t) -> unpeel_quants t
    | t -> t in

  let mapping = Hashtbl.create 64 in
  let rec is_general_enough = function
    | [] -> true
    | (TRigid v, r) :: xs -> begin
      match (Hashtbl.find_opt mapping v, r) with
        | (Some (TRigid p), TRigid r) ->
          if p = r then is_general_enough xs
          else false
        | (Some p, r) -> is_general_enough ((p, r) :: xs)
        | (None, r) ->
          Hashtbl.add mapping v r;
          is_general_enough xs
    end
    | (TVar p, TVar q) :: xs when p = q ->
      is_general_enough xs
    | ((TChr, TChr) | (TStr, TStr) | (TInt, TInt) | (TKind, TKind)) :: xs ->
      is_general_enough xs
    | (TArr (p, q), TArr (s, t)) :: xs
    | (TApp (p, q), TApp (s, t)) :: xs ->
      is_general_enough ((p, s) :: (q, t) :: xs)
    | (TTup xs, TTup ys) :: tl
    | (TCons (TCtorArr, xs), TCons (TCtorArr, ys)) :: tl ->
      tail tl (xs, ys)
    | (TCons (TCtorVar k1, xs), TCons (TCtorVar k2, ys)) :: tl when k1 == k2 ->
      tail tl (xs, ys)
    | _ -> false

  and tail acc = function
    | ([], []) -> is_general_enough acc
    | (x :: xs, y :: ys) -> tail ((x, y) :: acc) (xs, ys)
    | _ -> false in

  is_general_enough [unpeel_quants a, unpeel_quants b]

let gen (ignore : V.Set.t) (t : t) : V.t list * t =
  let mapping = Hashtbl.create 64 in
  let quants = ref [] in
  let rec visit = function
    | TVar n -> begin
      match Hashtbl.find_opt mapping n with
        | Some n -> n
        | None ->
          (* always register it in the hashtbl *)
          if V.Set.mem n ignore then begin
            Hashtbl.add mapping n (TVar n);
            TVar n
          end else begin
            quants := n :: !quants;
            Hashtbl.add mapping n (TRigid n);
            TRigid n
          end
    end
    | TRigid _ | TChr | TStr | TInt | TKind as t -> t
    | TArr (p, q) ->
      let p = visit p in TArr (p, visit q)
    | TApp (p, q) ->
      let p = visit p in TApp (p, visit q)
    | TTup xs ->
      let xs = List.fold_left (fun acc x -> visit x :: acc) [] xs in
      TTup (List.rev xs)
    | TCons (k, xs) ->
      let xs = List.fold_left (fun acc x -> visit x :: acc) [] xs in
      TCons (k, List.rev xs)
    | TQuant _ -> failwith "Type should not have quantifiers" in

  let t = visit t in
  (List.rev !quants, t)

let rec eval (map : t V.Map.t) (env : V.Set.t) : t -> t = function
  | TRigid n as t -> V.Map.find_opt n map |> Option.value ~default:t
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
  | TVar _ | TRigid _ | TChr | TStr | TInt | TKind -> false
  | TArr (p, q) | TApp (p, q) -> contains_quant p || contains_quant q
  | TTup xs | TCons (_, xs) -> List.exists contains_quant xs

let rec contains_var n = function
  | TVar m -> n = m
  | TRigid _ | TChr | TStr | TInt | TKind -> false
  | TArr (p, q) | TApp (p, q) ->
    contains_var n p || contains_var n q
  | TTup xs | TCons (_, xs) ->
    List.exists (contains_var n) xs
  | TQuant (_, t) -> contains_var n t

let free_vars ?(acc = V.Set.empty) t =
  let rec loop acc = function
    | [] -> acc
    | TVar n :: xs -> loop (V.Set.add n acc) xs
    | (TRigid _ | TChr | TStr | TInt | TKind) :: xs -> loop acc xs
    | (TArr (p, q) | TApp (p, q)) :: xs -> loop acc (p :: q :: xs)
    | (TTup ys | TCons (_, ys)) :: xs -> loop acc (List.rev_append ys xs)
    | TQuant (_, t) :: xs -> loop acc (t :: xs) in
  loop acc [t]

let rec shallow_subst env = function
  | TVar n -> begin
    match V.Map.find_opt n env with
      | None -> (TVar n, env)
      | Some (TVar _ as t) ->
        (* do path compression *)
        let (s, env) = shallow_subst env t in
        if s = t then (s, env)
        else (s, V.Map.add n s env)
      | Some t -> (t, env)
  end
  | t -> (t, env)

let rec expand ?(ground = None) env = function
  | TRigid _ | TChr | TStr | TInt | TKind as t -> (t, env)
  | TArr (p, q) ->
    let (p, env) = expand env p in
    let (q, env) = expand env q in
    (TArr (p, q), env)
  | TApp (p, q) ->
    let (p, env) = expand env p in
    let (q, env) = expand env q in
    (TApp (p, q), env)
  | TTup xs ->
    let foldf (env, acc) x =
      let (x, env) = expand env x in
      (env, x :: acc) in
    let (env, xs) = List.fold_left foldf (env, []) xs in
    (TTup (List.rev xs), env)
  | TCons (k, xs) ->
    let foldf (env, acc) x =
      let (x, env) = expand env x in
      (env, x :: acc) in
    let (env, xs) = List.fold_left foldf (env, []) xs in
    (TCons (k, List.rev xs), env)
  | TVar n ->
    let (t, env) = shallow_subst env (TVar n) in
    if t = TVar n then
      (Option.value ~default:t ground, env)
    else begin
      let (t, env) = expand env t in
      (t, V.Map.add n t env)
    end
  | TQuant (n, t) ->
    let (t, env) = expand env t in
    (TQuant (n, t), env)

let init_last head tail =
  let rec loop acc head = function
    | [] -> (List.rev acc, head)
    | x :: xs -> loop (head :: acc) x xs in
  loop [] head tail

type bad_unify =
  | Mismatch of t * t
  | Cyclic of V.t * t

let explain ?(env = None) : bad_unify -> string = function
  | Cyclic (v, q) ->
    sprintf "Cannot unify recursive types %s and %s" (V.to_string v) (to_string q)
  | Mismatch (p, q) ->
    let (p, q) = match env with
      | None -> (p, q)
      | Some env ->
        let (p, env) = expand env p in
        let (q, _) = expand env q in
        (p, q) in
    sprintf "Cannot unify unrelated types %s and %s" (to_string p) (to_string q)

let unify (env : t V.Map.t) (rules : (t * t) list) =
  let rec loop env rem = function
    | [] -> (env, rem)
    | (p, q) :: tl ->
      let (p, env) = shallow_subst env p in
      let (q, env) = shallow_subst env q in
      let rec tail acc = function
        | ([], []) -> loop env rem (List.rev_append acc tl)
        | (x :: xs, y :: ys) -> tail ((x, y) :: acc) (xs, ys)
        | _ -> loop env (Mismatch (p, q) :: rem) tl in
      match (p, q) with
        | (TQuant _, _) | (_, TQuant _) ->
          failwith "UNKNOWN TQUANT DURING UNIFY STEP"

        | (TRigid p, TRigid q) when p = q ->
          loop env rem tl
        | (TChr, TChr) | (TStr, TStr) | (TInt, TInt)
        | (TKind, TKind) ->
          loop env rem tl

        | (TArr (f1, a1), TArr (f2, a2))
        | (TApp (f1, a1), TApp (f2, a2)) ->
          loop env rem ((f1, f2) :: (a1, a2) :: tl)

        | (TTup xs, TTup ys)
        | (TCons (TCtorArr, xs), TCons (TCtorArr, ys)) ->
          tail [] (xs, ys)

        | (TCons (TCtorVar k1, xs), TCons (TCtorVar k2, ys)) when k1 == k2 ->
          tail [] (xs, ys)

        | (TCons (k, x :: xs), TApp (f, a))
        | (TApp (f, a), TCons (k, x :: xs)) ->
          let (init, last) = init_last x xs in
          loop env rem ((TCons (k, init), f) :: (last, a) :: tl)

        | (TArr (p, q), TApp (f, a))
        | (TApp (f, a), TArr (p, q)) ->
          loop env rem ((TCons (TCtorArr, [p]), f) :: (q, a) :: tl)

        | (TVar p, TVar q) ->
          let ordering = V.compare p q in
          let env =
            if ordering < 0 then
              V.Map.add p (TVar q) env
            else if ordering > 0 then
              V.Map.add q (TVar p) env
            else env in
          loop env rem tl

        | (TVar n, t) | (t, TVar n) ->
          let (t, env) = expand env t in
          if contains_var n t then
            loop env (Cyclic (n, t) :: rem) tl
          else
            loop (V.Map.add n t env) rem tl

        | _ ->
          loop env (Mismatch (p, q) :: rem) tl in
  loop env [] rules