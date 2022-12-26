open Printf
module V = VarInfo

type literal = Ast.ast_lit
type name = (V.t * Type.t)

type expr =
  | EVar of name
  | ELit of literal
  | ERaise of string
  | ECons of string * expr list
  | ETup of expr list
  | EApp of expr * expr
  | EType of Type.t
  | ELam of name * expr
  | ECase of expr * (pat * expr) list
  | ELet of binding * expr

and pat =
  | PatIgnore
  | PatLit of literal
  | PatDecons of string * name list
  | PatUnpack of name list

and binding =
  | NonRec of name * expr
  | Rec of (name * expr) list

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
    | ECons (k, []) -> output_string ppf k
    | ELam (v, e) ->
      fprintf ppf "\\%a -> %a" output_name v (output 0) e
    | ECase (s, cases) ->
      fprintf ppf "match %a with { " (output 0) s;
      let iterf (p, e) = fprintf ppf "%a -> %a; " output_pat p (output 0) e in
      List.iter iterf cases;
      output_string ppf "}"
    | ELet (vb, e) ->
      fprintf ppf "let %a in %a" output_binding vb (output 0) e

    | EApp (p, q) ->
      fprintf ppf "%a %a" (output 1) p (output 2) q
    | ECons (k, args) ->
      output_string ppf k;
      List.iter (fprintf ppf " %a" (output 2)) args

    and adjust_prec prec = function
      | ELam _ | ELet _ as t when prec > 0 -> ETup [t]
      | EApp _ | ECons (_, _ :: _) as t when prec > 1 -> ETup [t]
      | t -> t in

  output 0 ppf e

let rec expand_type env = function
  | ELit _ | ERaise _ as t -> (t, env)
  | EVar (n, t) ->
    let (t, env) = Type.expand env t in
    (EVar (n, t), env)
  | EApp (p, q) ->
    let (p, env) = expand_type env p in
    let (q, env) = expand_type env q in
    (EApp (p, q), env)
  | EType t ->
    let (t, env) = Type.expand env t in
    (EType t, env)
  | ELam ((n, t), e) ->
    let (t, env) = Type.expand env t in
    let (e, env) = expand_type env e in
    (ELam ((n, t), e), env)
  | ELet (vb, e) ->
    let (vb, env) = expand_binding env vb in
    let (e, env) = expand_type env e in
    (ELet (vb, e), env)
  | ETup xs ->
    let (xs, env) = list_expand_type env xs in
    (ETup xs, env)
  | ECons (k, xs) ->
    let (xs, env) = list_expand_type env xs in
    (ECons (k, xs), env)
  | ECase (s, cases) ->
    let (s, env) = expand_type env s in
    let foldf (env, acc) (p, x) =
      let (x, env) = expand_type env x in
      (env, (p, x) :: acc) in
  let (env, cases) = List.fold_left foldf (env, []) cases in
  (ECase (s, List.rev cases), env)

and expand_binding env = function
  | NonRec ((n, t), i) ->
    let (i, env) = expand_type env i in
    let (t, env) = Type.expand env t in
    (NonRec ((n, t), i), env)
  | Rec xs ->
    let foldf (env, acc) ((n, t), i) =
      let (i, env) = expand_type env i in
      let (t, env) = Type.expand env t in
      (env, ((n, t), i) :: acc) in
    let (env, xs) = List.fold_left foldf (env, []) xs in
    (Rec (List.rev xs), env)

and list_expand_type env list =
  let foldf (env, acc) x =
    let (x, env) = expand_type env x in
    (env, x :: acc) in
  let (env, list) = List.fold_left foldf (env, []) list in
  (List.rev list, env)