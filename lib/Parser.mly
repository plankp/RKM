%{
open Ast
%}

%token LPAREN RPAREN RSQUARE LSQUARE LCURLY RCURLY
%token SEMI COMMA COLON SLASH ARROW IMPLIES
%token SET BAR NOT NEG OR AND
%token <string> OP_VPRE OP_VMUL OP_VADD OP_VRCN OP_VAPP OP_VCMP
%token <string> OP_DPRE OP_DMUL OP_DADD OP_DRCN OP_DAPP OP_DCMP
%token LET REC IN REF MATCH WITH IF THEN ELSE
%token EXTERN DEF TYPE TRAIT IMPL
%token UNDERSCORE
%token <string> IDCTOR IDVAR
%token <Z.t> INT
%token <string> STR
%token <Uchar.t> CHAR
%token EOF

%start <ast_toplevel list> prog
%start <ast_typ> repl_annot
%start <ast_expr> repl_expr

%on_error_reduce expr4
%on_error_reduce expr3
%on_error_reduce expr2_prefix
%on_error_reduce expr2_mul
%on_error_reduce expr2_add
%on_error_reduce expr2_rcn
%on_error_reduce expr2_app
%on_error_reduce expr2_cmp
%on_error_reduce expr2_and
%on_error_reduce expr2_or
%on_error_reduce expr2
%on_error_reduce expr

%on_error_reduce pat4
%on_error_reduce pat3
%on_error_reduce pat2_prefix
%on_error_reduce pat2_mul
%on_error_reduce pat2_add
%on_error_reduce pat2_rcn
%on_error_reduce pat2_app
%on_error_reduce pat2_cmp
%on_error_reduce pat2
%on_error_reduce pat

%on_error_reduce annot3
%on_error_reduce annot2
%on_error_reduce annot

%%

prog:
  | LCURLY; e = toplevels; RCURLY; EOF { e }
  | LCURLY; RCURLY; EOF { [] }

toplevels:
  | x = toplevel; SEMI; xs = toplevels { x :: xs }
  | x = toplevel; SEMI? { [x] }

toplevel:
  | DEF; vb = block_vbinds { TopDef vb }
  | EXTERN; vb = block_externs { TopExtern vb }
  | TYPE; vb = block_aliases { TopAlias vb }
  | e = expr { TopExpr e }

block_externs:
  | LCURLY; xs = externs; RCURLY { xs }

externs:
  | n = IDVAR; COLON; t = annot; SET; e = STR; SEMI; xs = externs { (n, t, e) :: xs }
  | n = IDVAR; COLON; t = annot; SET; e = STR; SEMI? { [(n, t, e)] }

block_aliases:
  | LCURLY; xs = aliases; RCURLY { xs }

aliases:
  | x = alias; SEMI; xs = aliases { x :: xs }
  | x = alias; SEMI? { [x] }

alias:
  | n = IDCTOR; args = IDVAR*; SET; t = annot { DefAlias (n, args, t) }
  | n = IDCTOR; args = IDVAR*; SET; LCURLY; ks = ctors; RCURLY { DefData (n, args, ks) }

ctors:
  | n = IDCTOR; args = annot3*; SEMI; xs = ctors { (n, args) :: xs }
  | n = IDCTOR; args = annot3*; SEMI? { [(n, args)] }
  | n = dop_name; args = annot3*; SEMI; xs = ctors { (n, args) :: xs }
  | n = dop_name; args = annot3*; SEMI? { [(n, args)] }

repl_expr:
  | LCURLY; e = expr; RCURLY; EOF { e }

expr:
  | e = expr2; COLON; t = annot { ExprTyped (e, t) }
  | e = expr2 { e }

expr2:
  | l = expr2_or; SET; r = expr2 { Binary ("=", l, r) }
  | e = expr2_or { e }

expr2_or:
  | l = expr2_or; OR; r = expr2_and { Binary ("||", l, r) }
  | e = expr2_and { e }

expr2_and:
  | l = expr2_and; AND; r = expr2_cmp { Binary ("&&", l, r) }
  | e = expr2_cmp { e }

expr2_cmp:
  | l = expr2_cmp; f = OP_VCMP; r = expr2_app { Binary (f, l, r) }
  | l = expr2_cmp; k = OP_DCMP; r = expr2_app { Cons ("(" ^ k ^ ")", [l; r]) }
  | e = expr2_app { e }

expr2_app:
  | l = expr2_rcn; f = OP_VAPP; r = expr2_app { Binary (f, l, r) }
  | l = expr2_rcn; k = OP_DAPP; r = expr2_app { Cons ("(" ^ k ^ ")", [l; r]) }
  | e = expr2_rcn { e }

expr2_rcn:
  | l = expr2_add; f = OP_VRCN; r = expr2_rcn { Binary (f, l, r) }
  | l = expr2_add; k = OP_DRCN; r = expr2_rcn { Cons ("(" ^ k ^ ")", [l; r]) }
  | e = expr2_add { e }

expr2_add:
  | l = expr2_add; BAR; r = expr2_mul { Binary ("|", l, r) }
  | l = expr2_add; NEG; r = expr2_mul { Binary ("-", l, r) }
  | l = expr2_add; f = OP_VADD; r = expr2_mul { Binary (f, l, r) }
  | l = expr2_add; k = OP_DADD; r = expr2_mul { Cons ("(" ^ k ^ ")", [l; r]) }
  | e = expr2_mul { e }

expr2_mul:
  | l = expr2_mul; f = OP_VMUL; r = expr2_prefix { Binary (f, l, r) }
  | l = expr2_mul; k = OP_DMUL; r = expr2_prefix { Cons ("(" ^ k ^ ")", [l; r]) }
  | e = expr2_prefix { e }

expr2_prefix:
  | NOT; e = expr2_prefix { Unary ("!", e) }
  | NEG; e = expr2_prefix { Unary ("-", e) }
  | f = OP_VPRE; e = expr2_prefix { Unary (f, e) }
  | k = OP_DPRE; e = expr2_prefix { Cons ("(" ^ k ^ ")", [e]) }
  | e = expr3 { e }

expr3:
  | k = dop_name; args = expr4+ { Cons (k, args) }
  | k = IDCTOR; args = expr4+ { Cons (k, args) }
  | f = expr4; args = expr4+ { List.fold_left (fun f a -> App (f, a)) f args }
  | e = expr4 { e }

expr4:
  | op = vop_name { Var op }
  | op = dop_name { Cons (op, []) }
  | v = IDVAR { Var v }
  | v = IDCTOR { Cons (v, []) }
  | REF { Cons ("ref", []) }
  | s = STR { Lit (LitStr s) }
  | z = INT { Lit (LitInt z) }
  | c = CHAR { Lit (LitChar c) }
  | LCURLY; RCURLY { Seq [] }
  | LCURLY; xs = exprs; RCURLY { Seq xs }
  | LSQUARE; RSQUARE { List [] }
  | LSQUARE; xs = list_expr(RSQUARE); RSQUARE { List xs }
  | LPAREN; RPAREN { Tup [] }
  | LPAREN; xs = list_expr(RPAREN); RPAREN {
    match xs with
      | [x] -> x
      | xs -> Tup xs }
  | IF; p = expr; SEMI?; THEN; t = expr; SEMI?; ELSE; f = expr {
    Cond (p, t, f) }
  | LET; vb = block_vbinds; IN; e = expr { Let (vb, e) }
  | LET; REC; vb = block_vbinds; IN; e = expr { LetRec (vb, e) }
  | MATCH; s = expr; WITH; k = block_cases { Case (s, k) }
  | SLASH; ps = pat4+; ARROW; e = expr { Lam (ps, e) }
  | SLASH; MATCH; k = block_cases { LamCase k }

vop_name:
  | LPAREN; BAR; RPAREN { "(|)" }
  | LPAREN; NOT; RPAREN { "(!)" }
  | LPAREN; NEG; RPAREN { "(-)" }
  | LPAREN; f = OP_VPRE; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_VMUL; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_VADD; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_VRCN; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_VAPP; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_VCMP; RPAREN { "(" ^ f ^ ")" }

dop_name:
  | LPAREN; f = OP_DPRE; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_DMUL; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_DADD; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_DRCN; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_DAPP; RPAREN { "(" ^ f ^ ")" }
  | LPAREN; f = OP_DCMP; RPAREN { "(" ^ f ^ ")" }

exprs:
  | x = expr; SEMI; xs = exprs { x :: xs }
  | x = expr; SEMI? { [x] }

list_expr(tag):
  | x = expr; COMMA; xs = list_expr(tag) { x :: xs }
  | x = expr { [x] }

block_cases:
  | LCURLY; xs = cases; RCURLY { xs }

cases:
  | p = pat; ARROW; e = expr; SEMI; xs = cases { (p, e) :: xs }
  | p = pat; ARROW; e = expr; SEMI? { [(p, e)] }

block_vbinds:
  | LCURLY; xs = vbinds; RCURLY { xs }

vbinds:
  | x = vbind; SEMI; xs = vbinds { x :: xs }
  | x = vbind; SEMI? { [x] }

vbind:
  | n = IDVAR; COLON; t = annot { DefAnnot (n, t) }
  | n = IDVAR; ps = pat4*; SET; e = expr { DefValue (n, ps, e) }
  | n = vop_name; COLON; t = annot { DefAnnot (n, t) }
  | n = vop_name; ps = pat4*; SET; e = expr { DefValue (n, ps, e) }

pat:
  | p = pat2; COLON; t = annot { PatternTyped (p, t) }
  | e = pat2 { e }

pat2:
  | l = pat2_cmp; BAR; r = pat2 { Alternate (l, r) }
  | e = pat2_cmp { e }

pat2_cmp:
  | l = pat2_cmp; k = OP_DCMP; r = pat2_app { Decons ("(" ^ k ^ ")", [l; r]) }
  | e = pat2_app { e }

pat2_app:
  | l = pat2_rcn; k = OP_DAPP; r = pat2_app { Decons ("(" ^ k ^ ")", [l; r]) }
  | e = pat2_rcn { e }

pat2_rcn:
  | l = pat2_add; k = OP_DRCN; r = pat2_rcn { Decons ("(" ^ k ^ ")", [l; r]) }
  | e = pat2_add { e }

pat2_add:
  | l = pat2_add; k = OP_DADD; r = pat2_mul { Decons ("(" ^ k ^ ")", [l; r]) }
  | e = pat2_mul { e }

pat2_mul:
  | l = pat2_mul; k = OP_DMUL; r = pat2_prefix { Decons ("(" ^ k ^ ")", [l; r]) }
  | e = pat2_prefix { e }

pat2_prefix:
  | NEG; z = INT { Match (LitInt (Z.neg z)) }
  | k = OP_DPRE; e = pat2_prefix { Decons ("(" ^ k ^ ")", [e]) }
  | e = pat3 { e }

pat3:
  | k = IDCTOR; args = pat4+ { Decons (k, args) }
  | k = dop_name; args = pat4+ { Decons (k, args) }
  | REF; args = pat4+ { Decons ("ref", args) }
  | e = pat4 { e }

pat4:
  | UNDERSCORE { Cap None }
  | n = IDVAR { Cap (Some n) }
  | k = IDCTOR { Decons (k, []) }
  | op = dop_name { Decons (op, []) }
  | REF { Decons ("ref", []) }
  | s = STR { Match (LitStr s) }
  | z = INT { Match (LitInt z) }
  | c = CHAR { Match (LitChar c) }
  | LSQUARE; RSQUARE { Delist [] }
  | LSQUARE; xs = list_pat(RSQUARE); RSQUARE { Delist xs }
  | LPAREN; RPAREN { Detup [] }
  | LPAREN; xs = list_pat(RPAREN); RPAREN {
    match xs with
      | [x] -> x
      | xs -> Detup xs }

list_pat(tag):
  | x = pat; COMMA; xs = list_pat(tag) { x :: xs }
  | x = pat { [x] }

repl_annot:
  | LCURLY; e = annot; RCURLY; EOF { e }

annot:
  | a = annot2; ARROW; r = annot { TypeApp (TypeApp (TypeCtor "(->)", a), r) }
  | e = annot2 { e }

annot2:
  | f = annot2; a = annot3 { TypeApp (f, a) }
  | e = annot3 { e }

annot3:
  | UNDERSCORE { TypeIgn }
  | n = IDVAR { TypeVar n }
  | k = IDCTOR { TypeCtor k }
  | REF { TypeCtor "ref" }
  | LSQUARE; RSQUARE { TypeCtor "[]" }
  | LSQUARE; e = annot; RSQUARE { TypeApp (TypeCtor "[]", e) }
  | LPAREN; ARROW; RPAREN { TypeCtor "(->)" }
  | LPAREN; RPAREN { TypeTup [] }
  | LPAREN; xs = list_annot; RPAREN {
    match xs with
      | [x] -> x
      | xs -> TypeTup xs }

list_annot:
  | x = annot; COMMA; xs = list_annot { x :: xs }
  | x = annot { [x] }