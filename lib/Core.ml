open Printf
module V = VarInfo

type literal = Ast.ast_lit
type name = (V.t * Type.t)

type expr =
  | EVar of name
  | ELit of literal
  | ERaise of string
  | ECons of string * Type.t * expr list  (* type is TCons on a variant *)
  | ETup of expr list
  | EApp of expr * expr
  | EType of Type.t
  | ELam of name * expr
  | ETyLam of V.t * expr
  | ECase of expr * (pat * expr) list
  | ELet of binding * expr
  | ESet of expr * int * expr (* for mutating refs... *)
  | EHole of expr ref (* for injecting things into exprs... *)

and pat =
  | PatIgnore
  | PatLit of literal
  | PatDecons of string * name list
  | PatUnpack of name list

and binding =
  | NonRec of name * expr
  | Rec of (name * expr) list

let mk_empty_hole () =
  let rec e = EHole r and r = ref e in
  (e, r)

let rec output_name ppf (v, t) =
  fprintf ppf "(%a : %a)" V.output v Type.output t

and output_pat ppf = function
  | PatIgnore -> output_string ppf "_"
  | PatLit v -> Ast.output_lit ppf v
  | PatDecons (k, args) ->
    output_string ppf k;
    List.iter (fprintf ppf " %a" output_name) args
  | PatUnpack [] -> output_string ppf "()"
  | PatUnpack (x :: xs) ->
    fprintf ppf "(%a" output_name x;
    List.iter (fprintf ppf ", %a" output_name) xs;
    output_string ppf ")"

and output_binding ppf = function
  | NonRec (b, i) -> output_bi_pair ppf (b, i)
  | Rec [] -> output_string ppf "rec { }"
  | Rec ((b, i) :: xs) ->
    fprintf ppf "rec { %a" output_bi_pair (b, i);
    List.iter (fprintf ppf " ; %a" output_bi_pair) xs;
    output_string ppf " }"

and output_bi_pair ppf (b, i) =
  fprintf ppf "%a = %a" output_name b output i

and output ppf (e : expr) =
  let rec output prec ppf e =
    match adjust_prec prec e with
    | EVar n -> output_name ppf n
    | ELit v -> Ast.output_lit ppf v
    | ERaise s -> fprintf ppf "(Raise# %s)" s
    | EType t -> fprintf ppf "(@%a)" Type.output t
    | ETup [] -> output_string ppf "()"
    | ETup (x :: xs) ->
      fprintf ppf "(%a" (output 0) x;
      List.iter (fprintf ppf ", %a" (output 0)) xs;
      output_string ppf ")"
    | ECons (k, ty, args) ->
      fprintf ppf "(%s" k;
      List.iter (fprintf ppf " %a" (output 2)) args;
      fprintf ppf " : %a)" Type.output ty
    | ELam (v, e) ->
      fprintf ppf "\\%a -> %a" output_name v (output 0) e
    | ETyLam (v, e) ->
      fprintf ppf "\\ @%a -> %a" V.output v (output 0) e
    | ECase (s, cases) ->
      fprintf ppf "match %a with { " (output 0) s;
      let iterf (p, e) = fprintf ppf "%a -> %a; " output_pat p (output 0) e in
      List.iter iterf cases;
      output_string ppf "}"
    | ELet (vb, e) ->
      fprintf ppf "let %a in %a" output_binding vb (output 0) e

    | EApp (p, q) ->
      fprintf ppf "%a %a" (output 1) p (output 2) q

    | ESet (d, idx, s) ->
      fprintf ppf "%a.%d = %a" (output 2) d idx (output 0) s

    | EHole { contents = chain } as t ->
      if t == chain then output_string ppf "[#]"
      else fprintf ppf "[%a]" (output 0) chain

    and adjust_prec prec = function
      | ETyLam _ | ELam _ | ELet _ | ESet _ as t when prec > 0 -> ETup [t]
      | EApp _ as t when prec > 1 -> ETup [t]
      | t -> t in

  output 0 ppf e

let rec collect_free : expr -> V.Set.t = function
  | ELit _ | ERaise _ | EType _ -> V.Set.empty
  | EVar (n, _) -> V.Set.singleton n
  | EApp (p, q) | ESet (p, _, q) ->
    V.Set.union (collect_free p) (collect_free q)
  | ECons (_, _, xs) | ETup xs ->
    let foldf s k = V.Set.union (collect_free k) s in
    List.fold_left foldf V.Set.empty xs
  | ELam ((n, _), e) -> V.Set.remove n (collect_free e)
  | ETyLam (_, e) -> collect_free e
  | ELet (NonRec ((n, _), i), e) ->
    V.Set.union (collect_free i) (V.Set.remove n (collect_free e))
  | ELet (Rec vb, e) ->
    let foldf (u, d) ((n, _), i) =
      (V.Set.union u (collect_free i), V.Set.add n d) in
    let (u, d) = List.fold_left foldf (collect_free e, V.Set.empty) vb in
    V.Set.diff u d
  | ECase (s, cases) ->
    let foldf d (p, e) =
      V.Set.union d (V.Set.diff (collect_free e) (collect_captures p)) in
    List.fold_left foldf (collect_free s) cases
  | EHole { contents = chain } as t ->
    if t == chain then V.Set.empty
    else collect_free chain

and collect_captures : pat -> V.Set.t = function
  | PatIgnore | PatLit _ -> V.Set.empty
  | PatDecons (_, xs) | PatUnpack xs ->
    List.fold_left (fun s (n, _) -> V.Set.add n s) V.Set.empty xs

(*
 * derived from OCaml's definition
 * https://v2.ocaml.org/manual/letrecvalues.html
 *)

let rec is_valid_rec (names : V.Set.t) (e : expr) : bool =
  not (is_immediately_linked names e) && is_statically_constructive names e

and is_statically_constructive (names : V.Set.t) : expr -> bool = function
  | EVar _ | ELam _ -> true
  | ECons (_, _, xs) | ETup xs ->
    List.for_all (is_statically_constructive names) xs
  | ELet (NonRec ((name, _), i), e) ->
    is_statically_constructive names i &&
    is_statically_constructive (V.Set.add name names) e
  | ELet (Rec vb, e) ->
    let rec loop dset = function
      | [] -> is_statically_constructive dset e
      | ((n, _), i) :: xs when is_statically_constructive names i ->
        loop (V.Set.add n dset) xs
      | _ -> false in
    loop names vb
  | EHole { contents = chain } as t when t != chain ->
    is_statically_constructive names chain
  | t -> V.Set.disjoint names (collect_free t)

and is_immediately_linked (names : V.Set.t) : expr -> bool = function
  | EVar (n, _) -> V.Set.mem n names
  | ELet (NonRec ((n, _), i), e) ->
    let names =
      if is_immediately_linked names i then V.Set.add n names
      else names in
    is_immediately_linked names e
  | ELet (Rec vb, e) ->
    let foldf dset ((n, _), i) =
      if is_immediately_linked names i then V.Set.add n dset
      else dset in
    let names = List.fold_left foldf names vb in
    is_immediately_linked names e
  | EHole { contents = chain } as t when t != chain ->
    is_immediately_linked names chain
  | _ -> false

let rec is_syntactic_value : expr -> bool = function
  | ECons (_, TCons (TCtorVar v, _), _) when v == Type.varRef -> false

  | EVar _ | ELit _ | ELam _ -> true
  | ECons (_, _, xs) | ETup xs -> List.for_all is_syntactic_value xs
  | ELet (NonRec (_, i), e) -> is_syntactic_value i && is_syntactic_value e
  | ELet (Rec vb, e) ->
    List.for_all (fun (_, i) -> is_syntactic_value i) vb && is_syntactic_value e
  | EHole { contents = chain } as t when t != chain -> is_syntactic_value chain
  | _ -> false

let rec normalize = function
  | (EVar _ | ELit _ | ERaise _) as t -> t
  | EHole { contents = chain } as t ->
    if chain == t then t else normalize chain
  | EType t -> EType (Type.normalize t)
  | ETup xs -> ETup (List.map normalize xs)
  | ECons (k, t, xs) -> ECons (k, t, List.map normalize xs)
  | EApp (p, q) -> EApp (normalize p, normalize q)
  | ELam (n, e) -> ELam (n, normalize e)
  | ETyLam (n, e) -> ETyLam (n, normalize e)
  | ECase (s, cases) ->
    ECase (normalize s, List.map (fun (p, e) -> (p, normalize e)) cases)
  | ELet (vb, e) -> ELet (normalize_binding vb, normalize e)
  | ESet (p, idx, q) -> ESet (normalize p, idx, normalize q)

and normalize_binding = function
  | NonRec (b, i) -> NonRec (b, normalize i)
  | Rec xs -> Rec (List.map (fun (b, i) -> (b, normalize i)) xs)