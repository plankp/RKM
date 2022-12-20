open Lexer
open Parser

let parse rule lexbuf =
  let token_seq : (token * position) Seq.t = fun () ->
    let rec loop next_pos first_tok =
      let (leads_line, pos, next_pos, tok) = read next_pos first_tok lexbuf in
      let tail () =
        match tok with
          | EOF -> Seq.Cons ((EOF, pos), fun () -> Seq.Nil)
          | _ -> Seq.Cons ((tok, pos), fun () -> loop next_pos false) in

      if leads_line then
        if first_tok || tok = LCURLY then tail ()
        else Seq.Cons ((LEADER_HINT pos.colno, pos), tail)
      else tail () in
    loop { lineno = 0; colno = 0; } true in

  try
    rule token_seq
  with
    | Lexer.Error (p, e) -> Result.Error (p, e)