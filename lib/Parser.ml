open Ast
open Seq
open Printf

type token =
(* special magical symbols *)
  | EOF
  | INDENT_HINT of int
  | LEADER_HINT of int

(* set of symbols *)
  | LPAREN
  | RPAREN
  | LCURLY
  | RCURLY
  | SEMI
  | COMMA
  | ARROW
  | SET

(* keywords and literals *)
  | LET
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
  | INDENT_HINT n -> fprintf ppf "{%d}" n
  | LEADER_HINT n -> fprintf ppf "<%d>" n
  | LPAREN -> fprintf ppf "LPAREN"
  | RPAREN -> fprintf ppf "RPAREN"
  | LCURLY -> fprintf ppf "LCURLY"
  | RCURLY -> fprintf ppf "RCURLY"
  | ARROW -> fprintf ppf "ARROW"
  | COMMA -> fprintf ppf "COMMA"
  | SEMI -> fprintf ppf "SEMI"
  | SET -> fprintf ppf "SET"
  | LET -> fprintf ppf "LET"
  | IN -> fprintf ppf "IN"
  | MATCH -> fprintf ppf "MATCH"
  | WITH -> fprintf ppf "WITH"
  | UNDERSCORE -> fprintf ppf "UNDERSCORE"
  | IDCTOR n -> fprintf ppf "IDCTOR: %s" n
  | IDVAR n -> fprintf ppf "IDVAR: %s" n

let ( let* ) = Result.bind

let peek_position tokens =
  match tokens () with
    | Cons ((t, p), tl) -> (p, fun () -> Cons ((t, p), tl))
    | v -> (dummy_pos, fun () -> v)

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

let expect_tok tok tokens err =
  match tokens () with
    | Cons ((t, p), tl) ->
      if t = tok then Ok ((t, p), tl) else Error (p, err)
    | _ -> Error (dummy_pos, err)

let skip_tab ?(m=(~-1)) tokens =
  match tokens () with
    | Cons ((LEADER_HINT n, _), tl) when m = ~-1 || n >= m -> tl
    | v -> fun () -> v

let parse_block rule tokens =
  let parse_entries m tokens =
    let rec loop acc allow_semi tokens =
      let tail tl =
        let* (e, tl) = rule m tl in
        match e with
          | Some e -> loop (e :: acc) true tl
          | None -> Ok (List.rev acc, tl) in
      match tokens () with
        | Cons ((LEADER_HINT _, _), tl) when m = ~-1 -> loop acc allow_semi tl
        | Cons ((LEADER_HINT n, _), tl) when n = m -> tail tl
        | Cons ((SEMI, _), tl) when allow_semi -> loop acc false tl
        | v -> tail (fun () -> v) in
    loop [] false tokens in

  match tokens () with
    | Cons ((INDENT_HINT n, _), tl) -> parse_entries n tl
    | Cons ((LCURLY, _), tl) ->
      let* (acc, tl) = parse_entries ~-1 tl in
      let* (_, tl) = expect_tok RCURLY tl "missing '}'" in
      Ok (acc, tl)
    | Cons ((_, p), _) -> Error (p, "missing aligned block")
    | _ -> Error (dummy_pos, "missing aligned block")

let dump_tokens tokens =
  let iterf (tok, p) =
    printf "(%d, %d) %a\n" (p.lineno + 1) (p.colno + 1) output_token tok in
  Seq.iter iterf tokens

let rec prog tokens =
  parse_block expr tokens

and expr m tokens =
  let tokens = skip_tab ~m tokens in
  match tokens () with
    | Cons ((LET, _), tl) ->
      let* (vb, tl) = expect_some (parse_block binding) tl "missing bindings" in
      let* (_, tl) = expect_tok IN (skip_tab tl) "missing 'in'" in
      let* (e, tl) = expect_rule (expr m) tl "missing body" in
      Ok (Some (Let (vb, e)), tl)
    | Cons ((MATCH, _), tl) ->
      let* (s, tl) = expect_rule (expr ~-1) tl "missing scrutinee" in
      let* (_, tl) = expect_tok WITH (skip_tab tl) "missing 'with'" in
      let* (cases, tl) = expect_some (parse_block case) tl "missing cases" in
      Ok (Some (Case (s, cases)), tl)
    | v -> expr2 m (fun () -> v)

and expr2 m tokens =
  let* (f, tl) = expr3 m tokens in
  match f with
    | Some f ->
      let rec loop f tl =
        let* (v, tl) = expr3 m tl in
        match v with
          | Some v -> loop (App (f, v)) tl
          | None -> Ok (Some f, tl) in
      loop f tl
    | t -> Ok (t, tl)

and expr3 m tokens =
  let tokens = skip_tab ~m tokens in
  match tokens () with
    | Cons ((IDVAR v, _), tl) -> Ok (Some (Var v), tl)
    | Cons ((LPAREN, _), tl) -> begin
      let tl = skip_tab tl in
      match tl () with
        | Cons ((RPAREN, _), tl) -> Ok (Some (Tup []), tl)
        | v ->
          let rec loop acc tl =
            (* this is enclosed, so allow free-form (unaligned) expressions *)
            let* (e, tl) = expect_rule (expr ~-1) tl "missing expression" in
            let tl = skip_tab tl in
            match tl () with
              | Cons ((RPAREN, _), tl) ->
                if acc = [] then Ok (Some e, tl)
                else Ok (Some (Tup (List.rev_append acc [e])), tl)
              | Cons ((COMMA, _), tl) -> loop (e :: acc) tl
              | Cons ((_, p), _) -> Error (p, "unclosed parenthesized expression")
              | _ -> Error (dummy_pos, "unclosed parenthesized expression") in
          loop [] (fun () -> v)
    end
    | v -> Ok (None, fun () -> v)

and binding m tokens =
  match tokens () with
    | Cons ((IDVAR n, _), tl) ->
      (* setup the alignment to be just after the variable *)
      let m = if m = ~-1 then m else m + 1 in
      let tl = skip_tab ~m tl in
      let* (_, tl) = expect_tok SET tl "missing '='" in
      let tl = skip_tab ~m tl in
      let* (e, tl) = expect_rule (expr m) tl "missing initializer" in
      Ok (Some (n, e), tl)
    | v -> Ok (None, fun () -> v)

and case m tokens =
  (* setup the aligment to be just after the pattern *)
  let m = if m = ~-1 then m else m + 1 in
  let* (p, tl) = pat m tokens in
  match p with
    | None -> Ok (None, tl)
    | Some p ->
      let tl = skip_tab ~m tl in
      let* (_, tl) = expect_tok ARROW tl "missing '->'" in
      let* (e, tl) = expect_rule (expr m) tl "missing expression" in
      Ok (Some (p, e), tl)

and pat m tokens =
  pat3 m tokens

and pat3 m tokens =
  let tl = skip_tab ~m tokens in
  match tl () with
    | Cons ((IDCTOR k, _), tl) ->
      let rec loop acc tl =
        let* (v, tl) = pat4 m tl in
        match v with
          | Some v -> loop (v :: acc) tl
          | None -> Ok (Some (Decons (k, List.rev acc)), tl) in
      loop [] tl
    | v -> pat4 m (fun () -> v)

and pat4 m tokens =
  let tl = skip_tab ~m tokens in
  match tl () with
    | Cons ((UNDERSCORE, _), tl) -> Ok (Some (Cap None), tl)
    | Cons ((IDVAR n, _), tl) -> Ok (Some (Cap (Some n)), tl)
    | Cons ((IDCTOR k, _), tl) -> Ok (Some (Decons (k, [])), tl)
    | v -> Ok (None, fun () -> v)
