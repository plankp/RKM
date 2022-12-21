open Ast
open Seq
open Printf

type token =
(* special magical symbols *)
  | EOF

(* set of symbols *)
  | LPAREN
  | RPAREN
  | LCURLY
  | RCURLY
  | SEMI
  | COMMA
  | ARROW
  | OPSEQ of string

(* keywords and literals *)
  | LET
  | REC
  | IN
  | MATCH
  | WITH
  | UNDERSCORE
  | IDCTOR of string
  | IDVAR of string

type position = {
  lineno : int;
  colno : int;
}

let dummy_pos : position = { lineno = ~-1; colno = ~-1 }

let output_token ppf = function
  | EOF -> fprintf ppf "EOF"
  | LPAREN -> fprintf ppf "LPAREN"
  | RPAREN -> fprintf ppf "RPAREN"
  | LCURLY -> fprintf ppf "LCURLY"
  | RCURLY -> fprintf ppf "RCURLY"
  | ARROW -> fprintf ppf "ARROW"
  | COMMA -> fprintf ppf "COMMA"
  | SEMI -> fprintf ppf "SEMI"
  | LET -> fprintf ppf "LET"
  | REC -> fprintf ppf "REC"
  | IN -> fprintf ppf "IN"
  | MATCH -> fprintf ppf "MATCH"
  | WITH -> fprintf ppf "WITH"
  | UNDERSCORE -> fprintf ppf "UNDERSCORE"
  | IDCTOR n -> fprintf ppf "IDCTOR: %s" n
  | IDVAR n -> fprintf ppf "IDVAR: %s" n
  | OPSEQ s -> fprintf ppf "OPSEQ: %s" s

let ( let* ) = Result.bind

let peek_position tokens =
  match tokens () with
    | Cons ((t, p, f), tl) -> (p, fun () -> Cons ((t, p, f), tl))
    | v -> (dummy_pos, fun () -> v)

let fetch_tokens n tokens =
  let rec loop acc n tokens =
    if n <= 0 then (List.rev acc, tokens)
    else match tokens () with
      | Nil -> (List.rev acc, fun () -> Nil)
      | Cons (data, tl) -> loop (data :: acc) (n - 1) tl in
  loop [] n tokens

let unfetch_tokens unfetch tokens =
  List.fold_right (fun t tl () -> Cons (t, tl)) unfetch tokens

let obeys_alignment m pos first_tok =
  not first_tok || pos.colno >= m

let expect_rule rule tokens err =
  let* (v, tl) = rule tokens in
  match v with
    | Some v -> Ok (v, tl)
    | None ->
      let (p, _) = peek_position tl in
      Error (p, err)

let expect_some rule tokens err =
  let* (acc, tl) = rule tokens in
  match acc with
    | _ :: _ -> Ok (acc, tl)
    | [] ->
      let (p, _) = peek_position tl in
      Error (p, err)

let expect_tok ?(m = ~-1) tok tokens err =
  match tokens () with
    | Cons ((t, p, f), tl) ->
      if t = tok && obeys_alignment m p f then Ok ((t, p, f), tl)
      else Error (p, err)
    | _ -> Error (dummy_pos, err)

let maybe_tok ?(m = ~-1) tok tokens =
  match tokens () with
    | Cons ((t, p, f), tl) when t = tok && obeys_alignment m p f -> (true, tl)
    | v -> (false, fun () -> v)

let parse_many m rule tokens =
  let rec loop acc tl =
    let* (v, tl) = rule m tl in
    match v with
      | Some v -> loop (v :: acc) tl
      | None -> Ok (List.rev acc, tl) in
  loop [] tokens

let parse_block rule tokens =
  let parse_entries m tokens =
    let rec loop acc allow_semi tokens =
      let tl = match tokens () with
        | Cons ((SEMI, p, f), tl) when allow_semi && obeys_alignment m p f -> tl
        | v -> fun () -> v in
      let* (e, tl) = rule m tl in
      match e with
        | Some e -> loop (e :: acc) true tl
        | None -> Ok (List.rev acc, tl) in
    loop [] false tokens in

  match tokens () with
    | Cons ((LCURLY, _, _), tl) ->
      let* (acc, tl) = parse_entries ~-1 tl in
      let* (_, tl) = expect_tok RCURLY tl "missing '}'" in
      Ok (acc, tl)
    | Cons ((_, p, _), _) as v -> parse_entries p.colno (fun () -> v)
    | _ -> Error (dummy_pos, "missing aligned block")

let dump_tokens tokens =
  let iterf (tok, p, _) =
    printf "(%d, %d) %a\n" (p.lineno + 1) (p.colno + 1) output_token tok in
  Seq.iter iterf tokens

let rec prog tokens =
  parse_block expr tokens

and expr m tokens =
  match tokens () with
    | Cons ((LET, p, f), tl) when obeys_alignment m p f ->
      let (recur, tl) = maybe_tok REC tl in
      let* (vb, tl) = expect_some (parse_block binding) tl "missing bindings" in
      let* (_, tl) = expect_tok IN tl "missing 'in'" in
      let* (e, tl) = expect_rule (expr m) tl "missing body" in
      Ok (Some (Let (recur, vb, e)), tl)
    | Cons ((MATCH, p, f), tl) when obeys_alignment m p f ->
      let* (s, tl) = expect_rule (expr ~-1) tl "missing scrutinee" in
      let* (_, tl) = expect_tok WITH tl "missing 'with'" in
      let* (cases, tl) = expect_some (parse_block case) tl "missing cases" in
      Ok (Some (Case (s, cases)), tl)
    | v -> expr2_infix m (fun () -> v)

and expr2_infix m tokens =
  let* (lhs, tl) = expr2_prefix m tokens in
  match lhs with
    | Some lhs ->
      let* (res, tl) = expr2_infix_tail lhs 0 m tl in
      Ok (Some res, tl)
    | t -> Ok (t, tl)

and expr2_infix_tail lhs prec m tokens =
  (* if unknown operator, return -1
   * if left assoc, return (level, level)
   * if right assoc, return (level, level - 1) *)
  let lookup_prec = function
    | "=" -> (1, 0)
    | "||" -> (2, 2)
    | "&&" -> (3, 3)
    | "::" -> (6, 5)
    | "<<" | ">>" -> (8, 8)
    | op ->
      if op = "" then (~-1, ~-1)
      else match op.[0] with
        | '!' | '=' | '<' | '>' -> (4, 4)
        | '@' -> (5, 4)
        | '+' | '-' | '|' | '^' -> (7, 7)
        | '*' | '/' | '%' | '&' -> (8, 8)
        | _ -> (~-1, ~-1) in

  match tokens () with
    | Cons ((OPSEQ op, p, f), tl) as v when obeys_alignment m p f ->
      let (lhs_prec, rhs_prec) = lookup_prec op in
      if prec >= lhs_prec then Ok (lhs, fun () -> v)
      else begin
        let* (rhs, tl) = expect_rule (expr2_prefix m) tl "missing expression after infix operator" in
        let* (rhs, tl) = expr2_infix_tail rhs rhs_prec m tl in
        expr2_infix_tail (Binary (op, lhs, rhs)) prec m tl
      end
    | v -> Ok (lhs, fun () -> v)

and expr2_prefix m tokens =
  let is_prefix = function
    | "!" | "-" -> true
    | v -> v <> "" && v.[0] = '~' in

  let rec loop acc tl =
    match tl () with
      | Cons ((OPSEQ op, p, f), tl) when is_prefix op && obeys_alignment m p f ->
        loop (op :: acc) tl
      | v ->
        let* (e, tl) = expr3 m (fun () -> v) in
        match e with
          | Some e ->
            Ok (Some (List.fold_left (fun e op -> Unary (op, e)) e acc), tl)
          | None ->
            if acc = [] then Ok (None, tl)
            else
              let (p, _) = peek_position tl in
              Error (p, "missing expression after prefix operator") in
  loop [] tokens

and expr3 m tokens =
  let* (f, tl) = expr4 m tokens in
  match f with
    | Some f ->
      let rec loop f tl =
        let* (v, tl) = expr4 m tl in
        match v with
          | Some v -> loop (App (f, v)) tl
          | None -> Ok (Some f, tl) in
      loop f tl
    | t -> Ok (t, tl)

and expr4 m tokens =
  match tokens () with
    | Cons ((IDVAR v, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Var v), tl)
    | Cons ((LPAREN, p, f), tl) when obeys_alignment m p f -> begin
      (* parenthesized expressions are free-form *)
      match fetch_tokens 2 tl with
        | ((OPSEQ op, _, _) :: (RPAREN, _, _) :: xs, tl) ->
          Ok (Some (Var ("(" ^ op ^ ")")), unfetch_tokens xs tl)
        | ((RPAREN, _, _) :: xs, tl) ->
          Ok (Some (Tup []), unfetch_tokens xs tl)
        | (xs, tl) ->
          let rec loop acc tl =
            let* (e, tl) = expect_rule (expr ~-1) tl "missing expression" in
            match tl () with
              | Cons ((RPAREN, _, _), tl) ->
                if acc = [] then Ok (Some e, tl)
                else Ok (Some (Tup (List.rev_append acc [e])), tl)
              | Cons ((COMMA, _, _), tl) -> loop (e :: acc) tl
              | Cons ((_, p, _), _) -> Error (p, "unclosed parenthesized expression")
              | _ -> Error (dummy_pos, "unclosed parenthesized expression") in
          loop [] (unfetch_tokens xs tl)
    end

    | v -> Ok (None, fun () -> v)

and binding m tokens =
  let tail n m tl =
    (* setup the alignment to be just after the variable *)
    let m = if m = ~-1 then m else m + 1 in
    let* (args, tl) = parse_many m pat4 tl in
    let* (_, tl) = expect_tok ~m (OPSEQ "=") tl "missing '='" in
    let* (e, tl) = expect_rule (expr m) tl "missing initializer" in
    Ok (Some (DefValue (n, args, e)), tl) in

  match fetch_tokens 3 tokens with
    | ((LPAREN, p, f) :: (OPSEQ op, _, _) :: (RPAREN, _, _) :: xs, tl) when obeys_alignment m p f ->
      tail ("(" ^ op ^ ")") m (unfetch_tokens xs tl)
    | ((IDVAR n, p, f) :: xs, tl) when obeys_alignment m p f ->
      tail n m (unfetch_tokens xs tl)
    | (xs, tl) -> Ok (None, unfetch_tokens xs tl)

and case m tokens =
  let* (p, tl) = pat m tokens in
  match p with
    | None -> Ok (None, tl)
    | Some p ->
      (* setup the aligment to be just after the pattern *)
      let m = if m = ~-1 then m else m + 1 in
      let* (_, tl) = expect_tok ~m ARROW tl "missing '->'" in
      let* (e, tl) = expect_rule (expr m) tl "missing expression" in
      Ok (Some (p, e), tl)

and pat m tokens =
  pat2_infix m tokens

and pat2_infix m tokens =
  let* (lhs, tl) = pat3 m tokens in
  match lhs with
    | Some lhs ->
      let* (res, tl) = pat2_infix_tail lhs 0 m tl in
      Ok (Some res, tl)
    | t -> Ok (t, tl)

and pat2_infix_tail lhs prec m tokens =
  match tokens () with
    | Cons ((OPSEQ "|", p, f), tl) when prec < 1 && obeys_alignment m p f ->
      let* (rhs, tl) = expect_rule (pat3 m) tl "missing pattern after cons operator" in
      let* (rhs, tl) = pat2_infix_tail rhs 0 m tl in
      pat2_infix_tail (Alternate (lhs, rhs)) prec m tl
    | Cons ((OPSEQ "::", p, f), tl) when prec < 2 && obeys_alignment m p f ->
      let* (rhs, tl) = expect_rule (pat3 m) tl "missing pattern after cons operator" in
      let* (rhs, tl) = pat2_infix_tail rhs 1 m tl in
      pat2_infix_tail (Decons ("(::)", [lhs; rhs])) prec m tl
    | v -> Ok (lhs, fun () -> v)

and pat3 m tokens =
  match tokens () with
    | Cons ((IDCTOR k, p, f), tl) when obeys_alignment m p f ->
      let* (args, tl) = parse_many m pat4 tl in
      Ok (Some (Decons (k, args)), tl)
    | v -> pat4 m (fun () -> v)

and pat4 m tokens =
  match tokens () with
    | Cons ((UNDERSCORE, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Cap None), tl)
    | Cons ((IDVAR n, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Cap (Some n)), tl)
    | Cons ((IDCTOR k, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Decons (k, [])), tl)
    | Cons ((LPAREN, p, f), tl) when obeys_alignment m p f -> begin
      (* parenthesized patterns are also free-form *)
      match tl () with
        | Cons ((RPAREN, _, _), tl) -> Ok (Some (Unpack []), tl)
        | v ->
          let rec loop acc tl =
            let* (e, tl) = expect_rule (pat ~-1) tl "missing pattern" in
            match tl () with
              | Cons ((RPAREN, _, _), tl) ->
                if acc = [] then Ok (Some e, tl)
                else Ok (Some (Unpack (List.rev_append acc [e])), tl)
              | Cons ((COMMA, _, _), tl) -> loop (e :: acc) tl
              | Cons ((_, p, _), _) -> Error (p, "unclosed parenthesized pattern")
              | _ -> Error (dummy_pos, "unclosed parenthesized pattern") in
          loop [] (fun () -> v)
    end

    | v -> Ok (None, fun () -> v)
