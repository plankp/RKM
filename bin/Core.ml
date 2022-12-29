open Printf
module T = Type

type expr =
  | EVar of string * Z.t * T.t
  | EType of T.t
  | ELam of string * Z.t * T.t * expr
  | ETyLam of string * Z.t * expr
  | EApp of expr * expr
  | ETup of expr list
  | ELet of string * Z.t * T.t * expr * expr

let rec output ppf = function
  | EVar (n, id, _) ->
    fprintf ppf "%s.%a" n Z.output id
  | EType t ->
    fprintf ppf "(@%a)" T.output t
  | ELam _ | ETyLam _ as t ->
    fprintf ppf "(%a)" collapse_lam t
  | EApp (p, q) ->
    fprintf ppf "(%a %a)" output p output q
  | ETup [] ->
    output_string ppf "()"
  | ETup (x :: xs) ->
    fprintf ppf "(%a" output x;
    List.iter (fprintf ppf " %a" output) xs;
    output_string ppf ")"
  | ELet (n, id, t, i, e) ->
    fprintf ppf "(let (%s.%a : %a) = %a in %a)" n Z.output id T.output t output i output e

and collapse_lam ppf = function
  | ELam (n, id, t, e) ->
    fprintf ppf "\\(%s.%a : %a) -> " n Z.output id T.output t;
    collapse_lam ppf e
  | ETyLam (n, id, e) ->
    fprintf ppf "\\%s.%a. " n Z.output id;
    collapse_lam ppf e
  | t -> output ppf t

let rec subst_type ?(rigid = T.NameMap.empty) ?(weak = T.NameMap.empty) : expr -> expr = function
  | EVar (n, id, t) -> EVar (n, id, T.subst ~rigid ~weak t)
  | EType t -> EType (T.subst ~rigid ~weak t)
  | ELam (n, id, t, e) -> ELam (n, id, T.subst ~rigid ~weak t, subst_type ~rigid ~weak e)
  | ETyLam (n, id, e) ->
    let rigid = T.NameMap.remove (n, id) rigid in
    ETyLam (n, id, subst_type ~rigid ~weak e)
  | EApp (p, q) -> EApp (subst_type ~rigid ~weak p, subst_type ~rigid ~weak q)
  | ETup xs -> ETup (List.map (subst_type ~rigid ~weak) xs)
  | ELet (n, id, t, i, e) ->
    ELet (n, id, T.subst ~rigid ~weak t, subst_type ~rigid ~weak i, subst_type ~rigid ~weak e)