open Printf

type ast_expr =
  | Var of string
  | Lit of ast_lit
  | Tup of ast_expr list
  | Cons of string * ast_expr list
  | Lam of ast_pat list * ast_expr
  | App of ast_expr * ast_expr
  | Unary of string * ast_expr
  | Binary of string * ast_expr * ast_expr
  | Let of bool * ast_vdef list * ast_expr
  | Case of ast_expr * (ast_pat * ast_expr) list
  | Cond of ast_expr * ast_expr * ast_expr

and ast_pat =
  | Cap of string option
  | Match of ast_lit
  | Decons of string * ast_pat list
  | Unpack of ast_pat list
  | Alternate of ast_pat * ast_pat

and ast_vdef =
  | DefValue of string * ast_pat list * ast_expr

and ast_lit =
  | LitInt of Z.t
  | LitStr of string
  | LitChar of Uchar.t

let rec output ppf = function
  | Var x -> output_string ppf x
  | Lit lit -> output_lit ppf lit
  | App (p, q) -> fprintf ppf "(%a %a)" output p output q
  | Binary (op, p, q) -> fprintf ppf "(%a %s %a)" output p op output q
  | Unary (op, p) -> fprintf ppf "(%s%a)" op output p
  | Lam (args, e) ->
    output_string ppf "(\\";
    List.iter (fprintf ppf "%a " output_pat) args;
    fprintf ppf "-> %a)" output e;
  | Cons (k, []) -> output_string ppf k
  | Cons (k, xs) ->
    fprintf ppf "(%s" k;
    List.iter (fprintf ppf " %a" output) xs;
    output_string ppf ")"
  | Tup [] -> output_string ppf "()"
  | Tup (x :: xs) ->
    fprintf ppf "(%a" output x;
    List.iter (fprintf ppf ", %a" output) xs;
    output_string ppf ")"
  | Let (recur, vb, e) ->
    output_string ppf (if recur then "let rec {" else "let {");
    List.iter (fprintf ppf " %a;" output_vdef) vb;
    fprintf ppf " } in %a" output e
  | Case (s, cases) ->
    fprintf ppf "match %a with {" output s;
    List.iter (fun (p, e) -> fprintf ppf " %a -> %a;" output_pat p output e) cases;
    output_string ppf " }"
  | Cond (k, t, f) ->
    fprintf ppf "if %a then %a else %a" output k output t output f

and output_pat ppf = function
  | Cap None -> output_string ppf "_"
  | Cap (Some v) | Decons (v, []) -> output_string ppf v
  | Match lit -> output_lit ppf lit
  | Alternate (p, q) ->
    fprintf ppf "(%a|%a)" output_pat p output_pat q
  | Decons (k, xs) ->
    fprintf ppf "(%s" k;
    List.iter (fprintf ppf " %a" output_pat) xs;
    output_string ppf ")"
  | Unpack [] -> output_string ppf "()"
  | Unpack (x :: xs) ->
    fprintf ppf "(%a" output_pat x;
    List.iter (fprintf ppf ", %a" output_pat) xs;
    output_string ppf ")"

and output_vdef ppf = function
  | DefValue (n, args, e) ->
    output_string ppf n;
    List.iter (fprintf ppf " %a" output_pat) args;
    fprintf ppf " = %a" output e

and output_lit ppf = function
  | LitInt n ->
    if Z.sign n >= 0 then Z.output ppf n
    else fprintf ppf "(%a)" Z.output n
  | LitStr s -> fprintf ppf "%S" s
  | LitChar c ->
    let c = Uchar.to_int c in
    if c < 0x10000 then fprintf ppf "'\\u%04x'" c
    else fprintf ppf "'\\U%06x'" c