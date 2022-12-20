open Lexer
open Parser

let parse rule lexbuf =
  let token_seq : token Seq.t = fun () ->
    let rec loop colpos first_tok =
      let (leads_line, alignpos, colpos, tok) = read colpos first_tok lexbuf in
      let tail () =
        match tok with
          | EOF ->
            Seq.Cons (EOF, fun () -> Seq.Nil)
          | LET | WITH ->
            Seq.Cons (tok, fun () ->
              let (_, alignpos, colpos, tok) = read colpos false lexbuf in
              let tail () = Seq.Cons (tok, fun () -> loop colpos false) in
              if tok = LCURLY then tail ()
              else Seq.Cons (INDENT_HINT alignpos, tail))
          | _ -> Seq.Cons (tok, fun () -> loop colpos false) in

      if leads_line then
        (* there is an implicit alignment hint at the start of the file *)
        if tok = LCURLY then tail ()
        else if first_tok then Seq.Cons (INDENT_HINT alignpos, tail)
        else Seq.Cons (LEADER_HINT alignpos, tail)
      else tail () in
    loop 0 true in

  try
    rule token_seq
  with
    | Lexer.Error e -> Result.Error e