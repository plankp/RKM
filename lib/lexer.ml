type srcpos = {
  lineno : int32;       (* 1-based *)
  colno : int32;        (* 1-based byte offset *)
}

type lexeme =
  | Fixed of string     (* operators and keywords *)
  | Ctor of string      (* constructor identifier *)
  | Ident of string     (* general identifier *)
  | IntLit of Z.t       (* numeric literal *)
  | StrLit of string    (* string literal *)
  | ChrLit of Uchar.t   (* character literal *)
  | Eof

type state = {
  comment_depth : int;
  drop_line : bool;
  pos : srcpos;

  errors : (srcpos * string) list;
  tokens : (srcpos * lexeme) list;
}

let init_state : state = {
  comment_depth = 0;
  drop_line = false;
  pos = { lineno = 1l; colno = 1l };

  errors = [];
  tokens = [];
}

let to_result (s : state) =
  let errors =
    if s.comment_depth <> 0 then
      [(s.pos, "unterminated nested block comment")]
    else [] in
  let errors = List.rev_append s.errors errors in
  let tokens = List.rev_append s.tokens [(s.pos, Eof)] in
  (errors, tokens)

let rec drop (n : int) (stream : 'a Stream.t) =
  if n > 0 then
    try
      Stream.next stream |> ignore;
      drop (n - 1) stream
    with Stream.Failure -> stream
  else
    stream

let take (n : int) (stream : char Stream.t) =
  if n <= 0 then
    ""
  else begin
    let buf = Buffer.create n in
    let rec loop n =
      if n > 0 then
        try
          Stream.next stream |> Buffer.add_char buf;
          loop (n - 1)
        with Stream.Failure -> () in
    loop n;
    Buffer.contents buf
  end

let take_while (f : char -> bool) (stream : char Stream.t) =
  let buf = Buffer.create 16 in
  let rec loop () =
    match Stream.peek stream with
      | Some c when f c ->
        Stream.next stream |> Buffer.add_char buf;
        loop ()
      | _ -> Buffer.contents buf in
  loop ()

let take_digits (radix : int) (stream : char Stream.t) =
  if radix < 2 || radix > 36 then
    invalid_arg "Illegal radix not in [2, 36]"
  else
    let shamt = Z.of_int radix in
    let rec loop acc =
      let (width, repr) = match Stream.npeek 2 stream with
        | ['_'; ('A' .. 'Z') as c] -> (2, Char.code c - Char.code 'A' + 10)
        | ['_'; ('a' .. 'z') as c] -> (2, Char.code c - Char.code 'a' + 10)
        | ['_'; ('0' .. '9') as c] -> (2, Char.code c - Char.code '0')
        | ('A' .. 'Z') as c :: _ -> (1, Char.code c - Char.code 'A' + 10)
        | ('a' .. 'z') as c :: _ -> (1, Char.code c - Char.code 'a' + 10)
        | ('0' .. '9') as c :: _ -> (1, Char.code c - Char.code '0')
        | _ -> (0, radix) in
      if repr >= radix then
        acc
      else
        let _ = drop width stream in
        let (offset, value) = Option.value acc ~default:(0l, Z.zero) in
        let value = Z.add (Z.mul value shamt) (Z.of_int repr) in
        let offset = Int32.add offset (Int32.of_int width) in
        Some (offset, value) |> loop
      in
    loop None

let take_char (quote : char) (stream : char Stream.t) =
  let get_hex_tail width =
    let rec loop n acc tail =
      if n = 0 then
        Some acc
      else
        match tail with
          | ( '0' .. '9' as c ) :: tail ->
            loop (n - 1) (Char.code c - Char.code '0' + acc * 16) tail
          | ( 'A' .. 'F' as c ) :: tail ->
            loop (n - 1) (Char.code c - Char.code 'A' + 10 + acc * 16) tail
          | ( 'a' .. 'f' as c ) :: tail ->
            loop (n - 1) (Char.code c - Char.code 'a' + 10 + acc * 16) tail
          | _ -> None in
    Stream.npeek (width + 2) stream
      |> List.tl  (* skip backslash *)
      |> List.tl  (* skip [uU] *)
      |> loop width 0 in
  match Stream.npeek 2 stream with
    | '\\' :: 'U' :: _ ->
      get_hex_tail 6 |> Option.map (fun v -> let _ = drop 8 stream in (8l, v))
    | '\\' :: 'u' :: _ ->
      get_hex_tail 4 |> Option.map (fun v -> let _ = drop 6 stream in (6l, v))
    | '\\' :: 'n' :: _ ->
      let _ = drop 2 stream in Some (2l, Char.code '\n')
    | '\\' :: 't' :: _ ->
      let _ = drop 2 stream in Some (2l, Char.code '\t')
    | '\\' :: 'b' :: _ ->
      let _ = drop 2 stream in Some (2l, Char.code '\b')
    | '\\' :: 'r' :: _ ->
      let _ = drop 2 stream in Some (2l, Char.code '\r')
    | '\\' :: ( '\\' | '\'' | '"' as c ) :: _ ->
      let _ = drop 2 stream in Some (2l, Char.code c)
    | ( '\\' | '\r' | '\n' ) :: _ -> None (* illegal configurations *)
    | c :: _ when c <> quote ->
      Some (1l, Stream.next stream |> Char.code)
    | _ -> None

let ident_like_to_lexeme (seq : string) =
  match seq with
    | "" -> invalid_arg "Cannot convert empty sequence"
    | "type" | "data" | "def" | "let" | "match"
    | "if" | "then" | "else" | "and" | "or"
    | "in" | "true" | "false" | "_" -> Fixed seq
    | _ ->
      match seq.[0] with
        | 'A' .. 'Z' -> Ctor seq
        | _ -> Ident seq

let rec lex (stream : char Stream.t) (s : state) =
  let movecol n =
    let pos = { s.pos with
      colno = Int32.of_int n |> Int32.add s.pos.colno } in
    lex (drop n stream) { s with pos } in
  match Stream.npeek 2 stream with
    (* if there's nothing, then we're done *)
    | [] -> s

    (* always ignore (horizontal) space characters *)
    | ( ' ' | '\t' ) :: _ -> movecol 1

    (* newline handling for Windows *)
    | '\r' :: '\n' :: _ ->
      let pos = { colno = 1l; lineno = Int32.succ s.pos.lineno } in
      lex (drop 2 stream) { s with pos; drop_line = false }

    (* newline handling for Unix and old Macs *)
    | ( '\n' | '\r' ) :: _ ->
      let pos = { colno = 1l; lineno = Int32.succ s.pos.lineno } in
      lex (drop 1 stream) { s with pos; drop_line = false }

    (* start of a block comment *)
    | '/' :: '*' :: _ when not s.drop_line ->
      let s = { s with comment_depth = s.comment_depth + 1 } in
      let s =
        if s.comment_depth = 0 then
          { s with errors =
            (s.pos, "maximum comment nesting depth exceeded") :: s.errors }
        else s in
      let s =
        { s with pos = { s.pos with colno = Int32.add s.pos.colno 2l } } in
      lex (drop 2 stream) s

    (* end of a block comment *)
    | '*' :: '/' :: _ when not s.drop_line ->
      let s =
        if s.comment_depth = 0 then
          { s with errors =
            (s.pos, "invalid '*/' outside of comment context") :: s.errors }
        else { s with comment_depth = s.comment_depth - 1 } in
      let s =
        { s with pos = { s.pos with colno = Int32.add s.pos.colno 2l } } in
      lex (drop 2 stream) s

    (* typical ignore-while-we're-in-a-comment routine *)
    | _ when s.drop_line || s.comment_depth <> 0 -> movecol 1

    (* line comment *)
    | '/' :: '/' :: _ ->
      lex stream { s with drop_line = true }

    (* operators *)
    | ( '<' | '>' | '=' | '!' ) :: '=' :: _
    | '-' :: '>' :: _
    | ':' :: ':' :: _ ->
      let seq = take 2 stream in
      lex stream { s with
        pos = { s.pos with colno = Int32.add s.pos.colno 2l };
        tokens = (s.pos, Fixed seq) :: s.tokens }

    (* operators *)
    | ( '+' | '-' | '*' | '/' | '|'
      | '<' | '>' | '=' | '!' | ':'
      | '(' | ')' | ',' | ';' | '.' ) :: _ ->
      let seq = take 1 stream in
      lex stream { s with
        pos = { s.pos with colno = Int32.add s.pos.colno 1l };
        tokens = (s.pos, Fixed seq) :: s.tokens }

    (* character literal *)
    | '\'' :: _ ->
      let ipos = s.pos in
      let _ = drop 1 stream in
      let s = { s with pos = { ipos with colno = Int32.succ ipos.colno } } in
      let s = match take_char '\'' stream with
        | Some (width, value) when Uchar.is_valid value ->
          { s with
            pos = { s.pos with colno = Int32.add s.pos.colno width };
            tokens = (ipos, ChrLit (Uchar.of_int value)) :: s.tokens }
        | Some (width, _) ->
          { s with
            pos = { s.pos with colno = Int32.add s.pos.colno width };
            tokens = (ipos, ChrLit Uchar.min) :: s.tokens;
            errors = (s.pos, "invalid Unicode scalar value") :: s.errors }
        | _ ->
          { s with
            tokens = (ipos, ChrLit Uchar.min) :: s.tokens;
            errors = (s.pos, "missing encoded character") :: s.errors } in
      if Stream.peek stream = Some '\'' then
        lex (drop 1 stream) { s with
          pos = { s.pos with colno = Int32.succ s.pos.colno } }
      else
        lex stream { s with
          errors = (ipos, "unclosed character literal") :: s.errors }

    (* string literal *)
    | '\"' :: _ ->
      let buf = Buffer.create 16 in
      let ipos = s.pos in
      let rec loop s =
        match take_char '\"' stream with
          | Some (width, value) when Uchar.is_valid value ->
            Uchar.of_int value |> Buffer.add_utf_8_uchar buf;
            loop { s with
              pos = { s.pos with colno = Int32.add s.pos.colno width } }
          | Some (width, _) ->
            loop { s with
              pos = { s.pos with colno = Int32.add s.pos.colno width };
              errors = (s.pos, "invalid Unicode scalar value") :: s.errors }
          | _ ->
            let seq = Buffer.contents buf in
            match Stream.peek stream with
              | Some '\"' ->
                lex (drop 1 stream) { s with
                  pos = { s.pos with colno = Int32.succ s.pos.colno };
                  tokens = (ipos, StrLit seq) :: s.tokens }
              | _ ->
                lex stream { s with
                  tokens = (ipos, StrLit seq) :: s.tokens;
                  errors = (ipos, "unclosed string literal") :: s.errors } in
      let _ = drop 1 stream in
      loop { s with pos = { ipos with colno = Int32.succ ipos.colno } }

    (* binary integers *)
    | '0' :: ( 'b' | 'B' ) :: _ ->
      let _ = drop 2 stream in
      let s = { s with pos = { s.pos with colno = Int32.add s.pos.colno 2l } } in
      let s = match take_digits 2 stream with
        | Some (width, value) -> { s with
          pos = { s.pos with colno = Int32.add s.pos.colno width };
          tokens = (s.pos, IntLit value) :: s.tokens }
        | None -> { s with
          tokens = (s.pos, IntLit Z.zero) :: s.tokens;
          errors = (s.pos, "missing digits of binary integer") :: s.errors } in
      lex stream s

    (* octal integers *)
    | '0' :: ( 'c' | 'C' ) :: _ ->
      let _ = drop 2 stream in
      let s = { s with pos = { s.pos with colno = Int32.add s.pos.colno 2l } } in
      let s = match take_digits 8 stream with
        | Some (width, value) -> { s with
          pos = { s.pos with colno = Int32.add s.pos.colno width };
          tokens = (s.pos, IntLit value) :: s.tokens }
        | None -> { s with
          tokens = (s.pos, IntLit Z.zero) :: s.tokens;
          errors = (s.pos, "missing digits of octal integer") :: s.errors } in
      lex stream s

    (* hexadecimal integers *)
    | '0' :: ( 'x' | 'X' ) :: _ ->
      let _ = drop 2 stream in
      let s = { s with pos = { s.pos with colno = Int32.add s.pos.colno 2l } } in
      let s = match take_digits 16 stream with
        | Some (width, value) -> { s with
          pos = { s.pos with colno = Int32.add s.pos.colno width };
          tokens = (s.pos, IntLit value) :: s.tokens }
        | None -> { s with
          tokens = (s.pos, IntLit Z.zero) :: s.tokens;
          errors = (s.pos, "missing digits of hexadecimal integer") :: s.errors } in
      lex stream s

    (* 0 (because leading zeros are illegal) *)
    | '0' :: _ ->
      lex (drop 1 stream) { s with
        pos = { s.pos with colno = Int32.succ s.pos.colno };
        tokens = (s.pos, IntLit Z.zero) :: s.tokens }

    (* other decimal integers *)
    | '1' .. '9' :: _ ->
      let (width, value) = take_digits 10 stream |> Option.get in
      lex stream { s with
        pos = { s.pos with colno = Int32.add s.pos.colno width };
        tokens = (s.pos, IntLit value) :: s.tokens }

    (* identifier sequence *)
    | ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) :: _ ->
      let is_ident_part = function
        | ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' ) -> true
        | _ -> false in
      let seq = take_while is_ident_part stream in
      let width = seq |> String.length |> Int32.of_int in
      lex stream { s with
        pos = { s.pos with colno = Int32.add s.pos.colno width };
        tokens = (s.pos, ident_like_to_lexeme seq) :: s.tokens }

    (* if we don't match any token format, it's an error *)
    | _ ->
      let errors = (s.pos, "invalid source character") :: s.errors in
      let pos = { s.pos with colno = Int32.succ s.pos.colno } in
      lex (drop 1 stream) { s with pos; errors }
