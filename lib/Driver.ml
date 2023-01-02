open Lexing
module I = Parser.MenhirInterpreter

(* an abstract token with extra magic to deal with alignment *)
type abstrtok =
  | Shift of int
  | Align of int
  | Token of Parser.token

let get_colno p = p.pos_cnum - p.pos_bol + 1
let get_lineno p = p.pos_lnum + 1

let abstrtok_seq init_pos lexbuf =
  let rec loop endp pending first () =
    let ((leads_line, tok, startp, endp), pending) =
      read_next endp pending first in

    let n = get_colno startp in

    if tok = Parser.LCURLY then
      Seq.Cons ((Token tok, startp, endp), loop endp pending false)
    else if first then
      let pending = (false, tok, startp, endp) :: pending in
      Seq.Cons ((Shift n, startp, endp), loop endp pending false)
    else if leads_line then
      let pending = (false, tok, startp, endp) :: pending in
      Seq.Cons ((Align n, startp, endp), loop endp pending false)
    else
      (* for special tokens that are followed by a block, we need to handle
       * them here by marking the next iteration with [first] as true *)
      let p1 = (Token tok, startp, endp) in
      match tok with
        (* let and let rec are followed by a block *)
        | LET -> begin
          match read_next endp pending false with
            | ((leads_line, REC, startp, endp), pending) -> begin
              let p2 = (Token REC, startp, endp) in
              if leads_line then
                let n = get_colno startp in
                Seq.Cons (p1, fun () ->
                  Seq.Cons ((Align n, startp, endp), fun () ->
                    Seq.Cons (p2, loop endp pending true)))
              else
                Seq.Cons (p1, fun () ->
                  Seq.Cons (p2, loop endp pending true))
            end
            | (t, pending) ->
              Seq.Cons (p1, loop endp (t :: pending) true)
        end

        (* only \match is, \ alone is not *)
        | SLASH -> begin
          match read_next endp pending false with
            | ((leads_line, MATCH, startp, endp), pending) -> begin
              let p2 = (Token MATCH, startp, endp) in
              if leads_line then
                let n = get_colno startp in
                Seq.Cons (p1, fun () ->
                  Seq.Cons ((Align n, startp, endp), fun () ->
                    Seq.Cons (p2, loop endp pending true)))
              else
                Seq.Cons (p1, fun () ->
                  Seq.Cons (p2, loop endp pending true))
            end
            | (t, pending) ->
              Seq.Cons (p1, loop endp (t :: pending) false)
        end

        (* these ones are always followed by a block *)
        | DEF | EXTERN | TYPE | WITH ->
          Seq.Cons (p1, loop endp pending true)

        (* these ones are never blocks *)
        | _ ->
          Seq.Cons (p1, loop endp pending false)

  and read_next endp pending first =
    match pending with
      | x :: pending -> (x, pending)
      | [] ->
        let (leads_line, startp, endp, tok) = Lexer.read endp first lexbuf in
        ((leads_line, tok, startp, endp), []) in

  loop init_pos [] true

let rec loop seq depth (checkpoint : 'a I.checkpoint) =
  match checkpoint with
    | I.Accepted v ->
      Ok v

    | I.Rejected ->
      (* we don't try to recover an error, so this should not happen *)
      assert false

    | I.HandlingError env -> begin
      let s = I.current_state_number env in
      let (startp, _) = I.positions env in
      (* load the corresponding error message (if exists) from the
       * parser.messages file *)
      try
        (* we manually get rid of the extra \n tacked onto it *)
        let v = ParserMessages.message s in
        Error (startp, String.sub v 0 (String.length v - 1))
      with Not_found -> Error (startp, "syntax error")
    end

    | I.Shifting _ ->
      let checkpoint = I.resume checkpoint in
      loop seq depth checkpoint

    | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      loop seq depth checkpoint

    | I.InputNeeded _ -> begin
      match (seq (), depth) with
        | (Seq.Nil, _) ->
          failwith "IMPOSSIBLE SEQ STATE ENTERED"

        | (Seq.Cons ((Align n, startp, endp), seq), m :: ms) when m = n ->
          let checkpoint = I.offer checkpoint (SEMI, startp, endp) in
          loop seq (m :: ms) checkpoint
        | (Seq.Cons ((Align n, startp, endp) as atok, seq), m :: ms) when n < m ->
          let checkpoint = I.offer checkpoint (RCURLY, startp, endp) in
          loop (fun () -> Seq.Cons (atok, seq)) ms checkpoint
        | (Seq.Cons ((Align _, _, _), seq), ms) ->
          loop seq ms checkpoint

        | (Seq.Cons ((Shift n, startp, endp), seq), m :: ms) when n > m ->
          let checkpoint = I.offer checkpoint (LCURLY, startp, endp) in
          loop seq (n :: m :: ms) checkpoint
        | (Seq.Cons ((Shift n, startp, endp), seq), []) when n > 0 ->
          let checkpoint = I.offer checkpoint (LCURLY, startp, endp) in
          loop seq ([n]) checkpoint
        | (Seq.Cons ((Shift n, startp, endp), seq), ms) ->
          let checkpoint = I.offer checkpoint (LCURLY, startp, endp) in
          let seq = fun () ->
            Seq.Cons ((Token RCURLY, startp, endp), fun () ->
              Seq.Cons ((Align n, startp, endp), seq)) in
          loop seq (0 :: ms) checkpoint

        | (Seq.Cons ((Token RCURLY, startp, endp), seq), 0 :: ms) ->
          let checkpoint = I.offer checkpoint (RCURLY, startp, endp) in
          loop seq ms checkpoint
        | (Seq.Cons ((Token RCURLY, startp, endp), seq), ms) ->
          if I.acceptable checkpoint RCURLY startp then
            let checkpoint = I.offer checkpoint (RCURLY, startp, endp) in
            loop seq ms checkpoint
          else Error (startp, "mismatched '}'")

        | (Seq.Cons ((Token LCURLY, startp, endp), seq), ms) ->
          let checkpoint = I.offer checkpoint (LCURLY, startp, endp) in
          loop seq (0 :: ms) checkpoint

        | (Seq.Cons ((Token EOF, startp, endp) as atok, seq), m :: ms) when m <> 0 ->
          let checkpoint = I.offer checkpoint (RCURLY, startp, endp) in
          loop (fun () -> Seq.Cons (atok, seq)) ms checkpoint

        | (Seq.Cons ((Token t, startp, endp) as atok, seq), ms) ->
          match ms with
            | (m :: ms) when m <> 0 && not @@ I.acceptable checkpoint t startp ->
              let checkpoint = I.offer checkpoint (RCURLY, startp, endp) in
              loop (fun () -> Seq.Cons (atok, seq)) ms checkpoint
            | _ ->
              let checkpoint = I.offer checkpoint (t, startp, endp) in
              loop seq ms checkpoint
    end

let parse init_pos rule lexbuf =
  try
    init_pos |> rule |> loop (abstrtok_seq init_pos lexbuf) []
  with
    | Lexer.Error (p, e) -> Error (p, e)