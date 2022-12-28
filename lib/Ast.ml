open Printf

type ast_toplevel =
  | TopExpr of ast_expr
  | TopDef of ast_vdef list
  | TopExtern of ast_extern list
  | TopAlias of ast_alias list
  | TopData of ast_data list

and ast_expr =
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
  | Seq of ast_expr list
  | Let of ast_vdef list * ast_expr
  | LetRec of ast_vdef list * ast_expr
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

and ast_extern =
  string * ast_typ * string

and ast_alias =
  string * string list * ast_typ

and ast_data =
  string * string list * (string * ast_typ list) list

and ast_lit =
  | LitInt of Z.t
  | LitStr of string
  | LitChar of Uchar.t

let output_list ?(s = ",") fmt ppf xs =
  match xs with
    | [] -> ()  (* nothing to print *)
    | x :: xs ->
      fmt ppf x;
      List.iter (fprintf ppf "%s %a" s fmt) xs

let rec output_top ppf = function
  | TopExpr e -> output_expr ppf e
  | TopDef vb ->
    output_string ppf "def {";
    List.iter (fprintf ppf " %a;" output_vdef) vb;
    output_string ppf " }"
  | TopExtern vb ->
    let iterf (n, t, s) =
      fprintf ppf " %s : %a = %s;" n output_typ t s in
    output_string ppf "extern {";
    List.iter iterf vb;
    output_string ppf " }"
  | TopAlias vb ->
    let iterf (n, args, t) =
      fprintf ppf " %s" n;
      List.iter (fprintf ppf " %s") args;
      fprintf ppf " = %a;" output_typ t in
    output_string ppf "type {";
    List.iter iterf vb;
    output_string ppf " }"
  | TopData vb ->
    let iterf (n, args, ctors) =
      fprintf ppf " %s" n;
      List.iter (fprintf ppf " %s") args;
      let helper ppf (n, args) =
        fprintf ppf "%s" n;
        List.iter (fprintf ppf " %a" output_typ) args in
      fprintf ppf " = %a;" (output_list ~s:" |" helper) ctors in
    output_string ppf "data {";
    List.iter iterf vb;
    output_string ppf " }"

and output_expr ppf = function
  | Var x -> output_string ppf x
  | Lit lit -> output_lit ppf lit
  | App (p, q) -> fprintf ppf "(%a %a)" output_expr p output_expr q
  | Binary (op, p, q) -> fprintf ppf "(%a %s %a)" output_expr p op output_expr q
  | Unary (op, p) -> fprintf ppf "(%s%a)" op output_expr p
  | Lam (args, e) ->
    output_string ppf "(\\";
    List.iter (fprintf ppf "%a " output_pat) args;
    fprintf ppf "-> %a)" output_expr e;
  | LamCase cases ->
    output_string ppf "(\\match {";
    List.iter (fun (p, e) -> fprintf ppf " %a -> %a;" output_pat p output_expr e) cases;
    output_string ppf " })"
  | Cons (k, []) -> output_string ppf k
  | Cons (k, xs) ->
    fprintf ppf "(%s" k;
    List.iter (fprintf ppf " %a" output_expr) xs;
    output_string ppf ")"
  | Tup elts ->
    fprintf ppf "(%a)" (output_list output_expr) elts
  | List elts ->
    fprintf ppf "[%a]" (output_list output_expr) elts
  | Seq exprs ->
    fprintf ppf "{%a}" (output_list ~s:";" output_expr) exprs
  | Let (vb, e) ->
    output_string ppf "let {";
    List.iter (fprintf ppf " %a;" output_vdef) vb;
    fprintf ppf " } in %a" output_expr e
  | LetRec (vb, e) ->
    output_string ppf "let rec {";
    List.iter (fprintf ppf " %a;" output_vdef) vb;
    fprintf ppf " } in %a" output_expr e
  | Case (s, cases) ->
    fprintf ppf "match %a with {" output_expr s;
    List.iter (fun (p, e) -> fprintf ppf " %a -> %a;" output_pat p output_expr e) cases;
    output_string ppf " }"
  | Cond (k, t, f) ->
    fprintf ppf "if %a then %a else %a" output_expr k output_expr t output_expr f
  | ExprTyped (e, t) ->
    fprintf ppf "(%a : %a)" output_expr e output_typ t

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
    fprintf ppf " = %a" output_expr e
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