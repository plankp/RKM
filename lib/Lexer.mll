{
open Parser

exception Error of Parser.position * string

let str_to_int base str =
  let mult = Z.of_int base in
  let limit = String.length str in
  let rec loop acc i =
    if i >= limit then acc
    else
      match str.[i] with
        | '0' .. '9' as ch ->
          shift acc (Char.code ch - Char.code '0') (i + 1)
        | 'a' .. 'z' as ch ->
          shift acc (Char.code ch - Char.code 'a' + 10) (i + 1)
        | 'A' .. 'Z' as ch ->
          shift acc (Char.code ch - Char.code 'A' + 10) (i + 1)
        | _ -> loop acc (i + 1)
  and shift hi lo i =
    loop (Z.add (Z.mul hi mult) (Z.of_int lo)) i in
  loop Z.zero 0

let movecol pos n = { pos with colno = pos.colno + n }
let tabulate pos = { pos with colno = pos.colno land -8 + 8 }
let new_line pos = { lineno = pos.lineno + 1; colno = 0 }
}

let newline = '\n' | '\r' | "\r\n"
let id_ctor = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let id_var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let opchar = ['+' '-' '*' '/' '%' '!' '<' '=' '>' '|' '&' '^' '~' '@']

let digit_hex = ['a'-'f' 'A'-'F' '0'-'9']
let digit_dec = ['0'-'9']
let digit_oct = ['0'-'7']
let digit_bin = ['0' '1']

(* utf-8 decoding magic *)
let usv_1 = ['\x00'-'\x7F']
let usv_2 = ['\xC2'-'\xDF'] ['\x80'-'\xBF']
let usv_3 =  '\xE0' ['\xA0'-'\xBF'] ['\x80'-'\xBF']
  | (['\xE1'-'\xEC'] | ['\xEE'-'\xEF']) ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | '\xED' ['\x80'-'\x9F'] ['\x80'-'\xBF']
let usv_4 = '\xF0' ['\x90'-'\xBF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | ['\xF1'-'\xF3'] ['\x80'-'\xBF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | '\xF4' ['\x80'-'\x8F'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
let codepoint = usv_1 | usv_2 | usv_3 | usv_4

rule read pos first = parse
  (* comments *)
  | "//" { skip_line (movecol pos 2) lexbuf }
  | "/*" { skip_region 0 (movecol pos 2) first lexbuf }

  (* whitespace characters for dealing with alignment *)
  | ' ' { read (movecol pos 1) first lexbuf }
  | '\t' { read (tabulate pos) first lexbuf }
  | newline { read (new_line pos) true lexbuf }

  (* set of symbols *)
  | '(' { (first, pos, movecol pos 1, LPAREN) }
  | ')' { (first, pos, movecol pos 1, RPAREN) }
  | '[' { (first, pos, movecol pos 1, LSQUARE) }
  | ']' { (first, pos, movecol pos 1, RSQUARE) }
  | '{' { (first, pos, movecol pos 1, LCURLY) }
  | '}' { (first, pos, movecol pos 1, RCURLY) }
  | ';' { (first, pos, movecol pos 1, SEMI) }
  | ',' { (first, pos, movecol pos 1, COMMA) }
  | '\\' { (first, pos, movecol pos 1, SLASH) }
  | "->" { (first, pos, movecol pos 2, ARROW) }
  | "::" { (first, pos, movecol pos 2, OPSEQ "::") }
  | opchar+ {
    let s = Lexing.lexeme lexbuf in
    (first, pos, movecol pos (String.length s), OPSEQ s) }

  (* keywords and literals *)
  | "match" { (first, pos, movecol pos 5, MATCH) }
  | "with" { (first, pos, movecol pos 4, WITH) }
  | "then" { (first, pos, movecol pos 4, THEN) }
  | "else" { (first, pos, movecol pos 4, ELSE) }
  | "let" { (first, pos, movecol pos 3, LET) }
  | "rec" { (first, pos, movecol pos 3, REC) }
  | "in" { (first, pos, movecol pos 2, IN) }
  | "if" { (first, pos, movecol pos 2, IF) }
  | '_' { (first, pos, movecol pos 1, UNDERSCORE) }
  | '\'' { read_char [] first pos (movecol pos 1) lexbuf }
  | '\"' { read_string (Buffer.create 32) first pos (movecol pos 1) lexbuf }
  | ['1'-'9'] ('_'? digit_dec)* as tl {
    (first, pos, movecol pos (String.length tl), INT (str_to_int 10 tl)) }
  | '0' ['x' 'X'] ('_'? digit_hex)* as tl {
    (first, pos, movecol pos (String.length tl + 2), INT (str_to_int 16 tl)) }
  | '0' ['c' 'C'] ('_'? digit_oct)* as tl {
    (first, pos, movecol pos (String.length tl + 2), INT (str_to_int 8 tl)) }
  | '0' ['b' 'B'] ('_'? digit_bin)* as tl {
    (first, pos, movecol pos (String.length tl + 2), INT (str_to_int 2 tl)) }
  | '0' {
    (first, pos, movecol pos 1, INT Z.zero) }
  | id_ctor {
    let s = Lexing.lexeme lexbuf in
    (first, pos, movecol pos (String.length s), IDCTOR s) }
  | id_var {
    let s = Lexing.lexeme lexbuf in
    (first, pos, movecol pos (String.length s), IDVAR s) }

  (* everything else *)
  | eof { (first, pos, pos, EOF) }
  | codepoint { raise
    (Error (pos, "Illegal source character " ^ (Lexing.lexeme lexbuf))) }
  | _ { raise (Error (pos, "Illegal encoded character")) }

and skip_line pos = parse
  | newline { read (new_line pos) true lexbuf }
  | codepoint { skip_line (movecol pos 1) lexbuf }
  | _ { raise (Error (pos, "Invalid encoded character")) }
  | eof { (false, pos, pos, EOF) }

and skip_region depth pos first = parse
  | "/*" {
    if depth + 1 = 0 then
      raise (Error (pos, "Unsupported block comment nesting depth"))
    else skip_region (depth + 1) (movecol pos 2) first lexbuf }
  | "*/" {
    if depth = 0 then read (movecol pos 2) first lexbuf
    else skip_region (depth - 1) (movecol pos 2) first lexbuf }
  | newline { skip_region depth (new_line pos) true lexbuf }
  | codepoint { skip_region depth (movecol pos 1) false lexbuf }
  | _ { raise (Error (pos, "Invalid encoded character")) }
  | eof { raise (Error (pos, "Unterminated block comment")) }

and read_char lst first startpos pos = parse
  | '\'' {
    match lst with
      | [x] -> (first, startpos, movecol pos 1, CHAR x)
      | [] -> raise (Error (pos, "Empty character"))
      | _ -> raise (Error (pos, "Oversized character")) }
  | '\\' {
    let (pos, ch) = read_escape (movecol pos 1) lexbuf in
    read_char (ch :: lst) first startpos pos lexbuf }
  | ['\r' '\n'] { raise (Error (pos, "Invalid line break in character literal")) }

  (* crazy utf-8 decoding logic *)
  | usv_1 as ch {
    let lst = Uchar.of_char ch :: lst in
    read_char lst first startpos (movecol pos 1) lexbuf }
  | usv_2 as s {
    let ch1 = ((Char.code s.[0]) land 0x1F) lsl 6 in
    let ch2 = (Char.code s.[1]) land 0x3F in
    let lst = Uchar.of_int (ch1 lor ch2) :: lst in
    read_char lst first startpos (movecol pos 1) lexbuf }
  | usv_3 as s {
    let ch1 = ((Char.code s.[0]) land 0xF) lsl 12 in
    let ch2 = ((Char.code s.[1]) land 0x3F) lsl 6 in
    let ch3 = (Char.code s.[2]) land 0x3F in
    let lst = Uchar.of_int (ch1 lor ch2 lor ch3) :: lst in
    read_char lst first startpos (movecol pos 1) lexbuf }
  | usv_4 as s {
    let ch1 = ((Char.code s.[0]) land 0x7) lsl 18 in
    let ch2 = ((Char.code s.[1]) land 0x3F) lsl 12 in
    let ch3 = ((Char.code s.[2]) land 0x3F) lsl 6 in
    let ch4 = (Char.code s.[3]) land 0x3F in
    let lst = Uchar.of_int (ch1 lor ch2 lor ch3 lor ch4) :: lst in
    read_char lst first startpos (movecol pos 1) lexbuf }

  | _ { raise (Error (pos, "Invalid encoded character")) }
  | eof { raise (Error (pos, "Unterminated character")) }

and read_string buf first startpos pos = parse
  | '"' {
    (first, startpos, movecol pos 1, STR (Buffer.contents buf)) }
  | '\\' {
    let (pos, ch) = read_escape (movecol pos 1) lexbuf in
    Buffer.add_utf_8_uchar buf ch;
    read_string buf first startpos pos lexbuf }
  | ['\r' '\n'] { raise (Error (pos, "Invalid line break in string literal")) }
  | codepoint {
    Buffer.add_string buf (Lexing.lexeme lexbuf);
    read_string buf first startpos (movecol pos 1) lexbuf }
  | _ { raise (Error (pos, "Invalid encoded character")) }
  | eof { raise (Error (pos, "Unterminated string")) }

and read_escape pos = parse
  | [ '\\' '\'' '\"' ] as c { (movecol pos 1, Uchar.of_char c) }
  | 'b' { (movecol pos 1, Uchar.of_char '\b') }
  | 't' { (movecol pos 1, Uchar.of_char '\t') }
  | 'n' { (movecol pos 1, Uchar.of_char '\n') }
  | 'r' { (movecol pos 1, Uchar.of_char '\r') }
  | 'f' { (movecol pos 1, Uchar.of_char '\x0c') }
  | 'u' (digit_hex digit_hex digit_hex digit_hex as v) {
    (movecol pos 5, int_of_string ("0x" ^ v) |> Uchar.of_int) }
  | 'U' (digit_hex digit_hex digit_hex digit_hex digit_hex digit_hex as v) {
    (movecol pos 7, int_of_string ("0x" ^ v) |> Uchar.of_int) }
  | 'u' { raise (Error (pos, "Expected four hex digits to encode upto U+FFFF")) }
  | 'U' { raise (Error (pos, "Expected six hex digits to encode upto U+10FFFF")) }
  | codepoint {
    raise (Error (pos, "Unsupported escape character " ^ (Lexing.lexeme lexbuf))) }
  | _ { raise (Error (pos, "Illegal encoded character")) }
  | eof { raise (Error (pos, "Missing escape character")) }