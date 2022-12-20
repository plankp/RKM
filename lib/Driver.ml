open Lexer
open Parser

let parse rule lexbuf =
  let token_seq : (token * position * bool) Seq.t = fun () ->
    let rec loop next_pos first_tok =
      let (leads_line, pos, next_pos, tok) = read next_pos first_tok lexbuf in
        match tok with
          | EOF -> Seq.Cons ((EOF, pos, leads_line), fun () -> Seq.Nil)
          | _ -> Seq.Cons ((tok, pos, leads_line), fun () -> loop next_pos false) in
    loop { lineno = 0; colno = 0; } true in

  try
    rule token_seq
  with
    | Lexer.Error (p, e) -> Result.Error (p, e)