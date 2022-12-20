{
open Parser

exception Error of Parser.position * string

let movecol pos n = { pos with colno = pos.colno + n }
let tabulate pos = { pos with colno = pos.colno land -8 + 8 }
let new_line pos = { lineno = pos.lineno + 1; colno = 0 }
}

let newline = '\n' | '\r' | "\r\n"
let id_ctor = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let id_var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read pos first = parse
  (* comments *)
  | "//" { skip_line (movecol pos 2) lexbuf }

  (* whitespace characters for dealing with alignment *)
  | ' ' { read (movecol pos 1) first lexbuf }
  | '\t' { read (tabulate pos) first lexbuf }
  | newline { read (new_line pos) true lexbuf }

  (* set of symbols *)
  | "->" { (first, pos, movecol pos 2, ARROW) }
  | '(' { (first, pos, movecol pos 1, LPAREN) }
  | ')' { (first, pos, movecol pos 1, RPAREN) }
  | '{' { (first, pos, movecol pos 1, LCURLY) }
  | '}' { (first, pos, movecol pos 1, RCURLY) }
  | ';' { (first, pos, movecol pos 1, SEMI) }
  | ',' { (first, pos, movecol pos 1, COMMA) }
  | '=' { (first, pos, movecol pos 1, SET) }

  (* keywords and literals *)
  | "match" { (first, pos, movecol pos 5, MATCH) }
  | "with" { (first, pos, movecol pos 4, WITH) }
  | "let" { (first, pos, movecol pos 3, LET) }
  | "rec" { (first, pos, movecol pos 3, REC) }
  | "in" { (first, pos, movecol pos 2, IN) }
  | '_' { (first, pos, movecol pos 1, UNDERSCORE) }
  | id_ctor {
    let s = Lexing.lexeme lexbuf in
    (first, pos, movecol pos (String.length s), IDCTOR s) }
  | id_var {
    let s = Lexing.lexeme lexbuf in
    (first, pos, movecol pos (String.length s), IDVAR s) }

  (* everything else *)
  | eof { (first, pos, pos, EOF) }
  | _ { raise
    (Error (pos, "Illegal source character " ^ (Lexing.lexeme lexbuf))) }

and skip_line pos = parse
  | newline { read (new_line pos) true lexbuf }
  | _ { skip_line (movecol pos 1) lexbuf }
  | eof { (false, pos, pos, EOF) }
