open Printf
module V = VarInfo

type literal = Ast.ast_lit
type binding = (V.t * Type.t)

type expr =
  | EVar of binding
  | ELit of literal
  | ERaise of string
  | ECons of string * expr list
  | ETup of expr list
  | EApp of expr * expr
  | EType of Type.t
  | ELam of binding * expr
  | ECase of expr * (pat * expr) list
  | ELet of binding * expr * expr

and pat =
  | PatIgnore
  | PatLit of literal
  | PatDecons of string * binding list
  | PatUnpack of binding list

let output_binding ppf (v, t) =
  fprintf ppf "(%a : %a)" V.output v Type.output t

let output_pat ppf = function
  | PatIgnore -> output_string ppf "_"
  | PatLit v -> Ast.output_lit ppf v
  | PatDecons (k, args) ->
    output_string ppf k;
    List.iter (fprintf ppf " %a" output_binding) args
  | PatUnpack [] -> output_string ppf "()"
  | PatUnpack (x :: xs) ->
    fprintf ppf "(%a" output_binding x;
    List.iter (fprintf ppf ", %a" output_binding) xs;
    output_string ppf ")"

let output ppf (e : expr) =
  let rec output prec ppf e =
    match adjust_prec prec e with
    | EVar n -> output_binding ppf n
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
      fprintf ppf "(\\%a -> %a)" output_binding v (output 0) e
    | ECase (s, cases) ->
      fprintf ppf "match %a with { " (output 0) s;
      let iterf (p, e) = fprintf ppf "%a -> %a; " output_pat p (output 0) e in
      List.iter iterf cases;
      output_string ppf "}"
    | ELet (b, i, e) ->
      fprintf ppf "(let %a = %a in %a)"
        output_binding b (output 0) i (output 0) e

    | EApp (p, q) ->
      fprintf ppf "%a %a" (output 0) p (output 1) q
    | ECons (k, args) ->
      output_string ppf k;
      List.iter (fprintf ppf " %a" (output 1)) args

    and adjust_prec prec = function
      | EApp _ | ECons (_, _ :: _) as t when prec > 0 -> ETup [t]
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
  | ELet ((b, t), i, e) ->
    let (i, env) = expand_type env i in
    let (t, env) = Type.expand env t in
    let (e, env) = expand_type env e in
    (ELet ((b, t), i, e), env)
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

and list_expand_type env list =
  let foldf (env, acc) x =
    let (x, env) = expand_type env x in
    (env, x :: acc) in
  let (env, list) = List.fold_left foldf (env, []) list in
  (List.rev list, env)