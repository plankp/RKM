{
open Parser
open Lexing

exception Error of string

let tabulate col = col land -8 + 8
}

let newline = '\n' | '\r' | "\r\n"
let id_ctor = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let id_var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read colpos first = parse
  (* comments *)
  | "//" { skip_line colpos lexbuf }

  (* whitespace characters for dealing with alignment *)
  | ' ' { read (colpos + 1) first lexbuf }
  | '\t' { read (tabulate colpos) first lexbuf }
  | newline { new_line lexbuf; read 0 true lexbuf }

  (* set of symbols *)
  | "->" { (first, colpos, colpos + 2, ARROW) }
  | '(' { (first, colpos, colpos + 1, LPAREN) }
  | ')' { (first, colpos, colpos + 1, RPAREN) }
  | '{' { (first, colpos, colpos + 1, LCURLY) }
  | '}' { (first, colpos, colpos + 1, RCURLY) }
  | ';' { (first, colpos, colpos + 1, SEMI) }
  | ',' { (first, colpos, colpos + 1, COMMA) }
  | '=' { (first, colpos, colpos + 1, SET) }

  (* keywords and literals *)
  | "match" { (first, colpos, colpos + 5, MATCH) }
  | "with" { (first, colpos, colpos + 4, WITH) }
  | "let" { (first, colpos, colpos + 3, LET) }
  | "in" { (first, colpos, colpos + 2, IN) }
  | '_' { (first, colpos, colpos + 1, UNDERSCORE) }
  | id_ctor {
    let s = Lexing.lexeme lexbuf in
    (first, colpos, colpos + String.length s, IDCTOR s) }
  | id_var {
    let s = Lexing.lexeme lexbuf in
    (first, colpos, colpos + String.length s, IDVAR s) }

  (* everything else *)
  | eof { (first, colpos, colpos, EOF) }
  | _ { raise (Error ("Illegal source character " ^ (Lexing.lexeme lexbuf))) }

and skip_line colpos = parse
  | newline { new_line lexbuf; read 0 true lexbuf }
  | _ { skip_line (colpos + 1) lexbuf }
  | eof { (false, colpos, colpos, EOF) }
