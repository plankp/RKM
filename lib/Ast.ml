open Printf

type ast_expr =
  | Var of string
  | Lit of ast_lit
  | Tup of ast_expr list
  | List of ast_expr list
  | Cons of string * ast_expr list
  | Lam of ast_pat list * ast_expr
  | LamCase of (ast_pat * ast_expr) list
  | App of ast_expr * ast_expr
  | Unary of string * ast_expr
  | Binary of string * ast_expr * ast_expr
  | Let of bool * ast_vdef list * ast_expr
  | Case of ast_expr * (ast_pat * ast_expr) list
  | Cond of ast_expr * ast_expr * ast_expr
  | ExprTyped of ast_expr * ast_typ

and ast_pat =
  | Cap of string option
  | Match of ast_lit
  | Decons of string * ast_pat list
  | Detup of ast_pat list
  | Delist of ast_pat list
  | Alternate of ast_pat * ast_pat
  | PatternTyped of ast_pat * ast_typ

and ast_typ =
  | TypeIgn
  | TypeVar of string
  | TypeCtor of string
  | TypeApp of ast_typ * ast_typ
  | TypeTup of ast_typ list

and ast_vdef =
  | DefValue of string * ast_pat list * ast_expr
  | DefAnnot of string * ast_typ

and ast_lit =
  | LitInt of Z.t
  | LitStr of string
  | LitChar of Uchar.t

let output_list fmt ppf xs =
  match xs with
    | [] -> ()  (* nothing to print *)
    | x :: xs ->
      fmt ppf x;
      List.iter (fprintf ppf ", %a" fmt) xs

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
  | LamCase cases ->
    output_string ppf "(\\match {";
    List.iter (fun (p, e) -> fprintf ppf " %a -> %a;" output_pat p output e) cases;
    output_string ppf " })"
  | Cons (k, []) -> output_string ppf k
  | Cons (k, xs) ->
    fprintf ppf "(%s" k;
    List.iter (fprintf ppf " %a" output) xs;
    output_string ppf ")"
  | Tup elts ->
    fprintf ppf "(%a)" (output_list output) elts
  | List elts ->
    fprintf ppf "[%a]" (output_list output) elts
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
  | ExprTyped (e, t) ->
    fprintf ppf "(%a : %a)" output e output_typ t

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
  | Detup elts ->
    fprintf ppf "(%a)" (output_list output_pat) elts
  | Delist elts ->
    fprintf ppf "[%a]" (output_list output_pat) elts
  | PatternTyped (p, t) ->
    fprintf ppf "(%a : %a)" output_pat p output_typ t

and output_typ ppf = function
  | TypeIgn -> output_string ppf "_"
  | TypeVar n | TypeCtor n -> output_string ppf n
  | TypeApp (p, q) -> fprintf ppf "(%a %a)" output_typ p output_typ q
  | TypeTup elts ->
    fprintf ppf "(%a)" (output_list output_typ) elts

and output_vdef ppf = function
  | DefValue (n, args, e) ->
    output_string ppf n;
    List.iter (fprintf ppf " %a" output_pat) args;
    fprintf ppf " = %a" output e
  | DefAnnot (n, t) ->
    fprintf ppf "%s : %a" n output_typ t

and output_lit ppf = function
  | LitInt n ->
    if Z.sign n >= 0 then Z.output ppf n
    else fprintf ppf "(%a)" Z.output n
  | LitStr s -> fprintf ppf "%S" s
  | LitChar c ->
    let c = Uchar.to_int c in
    if c < 0x10000 then fprintf ppf "'\\u%04x'" c
    else fprintf ppf "'\\U%06x'" c