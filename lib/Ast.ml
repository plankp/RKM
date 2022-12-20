open Printf

type ast_expr =
  | Var of string
  | Tup of ast_expr list
  | App of ast_expr * ast_expr
  | Let of (string * ast_expr) list * ast_expr
  | Case of ast_expr * (ast_pat * ast_expr) list

and ast_pat =
  | Cap of string option
  | Decons of string * ast_pat list


let rec output ppf = function
  | Var x -> output_string ppf x
  | App (p, q) -> fprintf ppf "(%a %a)" output p output q
  | Tup [] -> output_string ppf "()"
  | Tup (x :: xs) ->
    fprintf ppf "(%a" output x;
    List.iter (fprintf ppf ", %a" output) xs;
    output_string ppf ")"
  | Let (vb, e) ->
    output_string ppf "let {";
    List.iter (fun (n, i) -> fprintf ppf " %s = %a;" n output i) vb;
    fprintf ppf " } in %a" output e
  | Case (s, cases) ->
    fprintf ppf "case %a of {" output s;
    List.iter (fun (p, e) -> fprintf ppf " %a -> %a;" output_pat p output e) cases;
    output_string ppf " }";

and output_pat ppf = function
  | Cap None -> output_string ppf "_"
  | Cap (Some v) | Decons (v, []) -> output_string ppf v
  | Decons (k, xs) ->
    fprintf ppf "(%s" k;
    List.iter (fprintf ppf " %a" output_pat) xs;
    output_string ppf ")"