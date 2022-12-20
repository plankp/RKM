open Lexer
open Parser

let parse rule lexbuf =
  let token_seq : (token * position) Seq.t = fun () ->
    let rec loop next_pos first_tok =
      let (leads_line, pos, next_pos, tok) = read next_pos first_tok lexbuf in
      let tail () =
        match tok with
          | EOF ->
            Seq.Cons ((EOF, pos), fun () -> Seq.Nil)
          | LET | WITH ->
            Seq.Cons ((tok, pos), fun () ->
              let (_, pos, next_pos, tok) = read next_pos false lexbuf in
              let tail () = Seq.Cons ((tok, pos), fun () -> loop next_pos false) in
              if tok = LCURLY then tail ()
              else Seq.Cons ((INDENT_HINT pos.colno, pos), tail))
          | _ -> Seq.Cons ((tok, pos), fun () -> loop next_pos false) in

      if leads_line then
        (* there is an implicit alignment hint at the start of the file *)
        if tok = LCURLY then tail ()
        else if first_tok then Seq.Cons ((INDENT_HINT pos.colno, pos), tail)
        else Seq.Cons ((LEADER_HINT pos.colno, pos), tail)
      else tail () in
    loop { lineno = 0; colno = 0; } true in

  try
    rule token_seq
  with
    | Lexer.Error (p, e) -> Result.Error (p, e)