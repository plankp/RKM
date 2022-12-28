open Ast
open Seq
open Printf

type token =
(* special magical symbols *)
  | EOF

(* set of symbols *)
  | LPAREN
  | RPAREN
  | RSQUARE
  | LSQUARE
  | LCURLY
  | RCURLY
  | SEMI
  | COMMA
  | COLON
  | SLASH
  | ARROW
  | IMPLIES
  | OPSEQ of string

(* keywords and literals *)
  | LET
  | REC
  | REF
  | IN
  | MATCH
  | WITH
  | IF
  | THEN
  | ELSE
  | EXTERN
  | DEF
  | DATA
  | TYPE
  | TRAIT
  | IMPL
  | UNDERSCORE
  | IDCTOR of string
  | IDVAR of string
  | INT of Z.t
  | STR of string
  | CHAR of Uchar.t

type position = {
  lineno : int;
  colno : int;
}

let dummy_pos : position = { lineno = ~-1; colno = ~-1 }

let output_token ppf = function
  | EOF -> fprintf ppf "EOF"
  | LPAREN -> fprintf ppf "LPAREN"
  | RPAREN -> fprintf ppf "RPAREN"
  | LSQUARE -> fprintf ppf "LSQUARE"
  | RSQUARE -> fprintf ppf "RSQUARE"
  | LCURLY -> fprintf ppf "LCURLY"
  | RCURLY -> fprintf ppf "RCURLY"
  | SLASH -> fprintf ppf "SLASH"
  | ARROW -> fprintf ppf "ARROW"
  | IMPLIES -> fprintf ppf "IMPLIES"
  | COMMA -> fprintf ppf "COMMA"
  | COLON -> fprintf ppf "COLON"
  | SEMI -> fprintf ppf "SEMI"
  | LET -> fprintf ppf "LET"
  | REC -> fprintf ppf "REC"
  | REF -> fprintf ppf "REF"
  | IN -> fprintf ppf "IN"
  | MATCH -> fprintf ppf "MATCH"
  | WITH -> fprintf ppf "WITH"
  | IF -> fprintf ppf "IF"
  | THEN -> fprintf ppf "THEN"
  | ELSE -> fprintf ppf "ELSE"
  | EXTERN -> fprintf ppf "EXTERN"
  | DEF -> fprintf ppf "DEF"
  | DATA -> fprintf ppf "DATA"
  | TYPE -> fprintf ppf "TYPE"
  | TRAIT -> fprintf ppf "TRAIT"
  | IMPL -> fprintf ppf "IMPL"
  | UNDERSCORE -> fprintf ppf "UNDERSCORE"
  | IDCTOR n -> fprintf ppf "IDCTOR: %s" n
  | IDVAR n -> fprintf ppf "IDVAR: %s" n
  | OPSEQ s -> fprintf ppf "OPSEQ: %s" s
  | INT z -> fprintf ppf "INT: %a" Z.output z
  | STR s -> fprintf ppf "STR: %S" s
  | CHAR c -> fprintf ppf "CHAR: U+%04X" (Uchar.to_int c)

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

let parse_many ?(m = ~-1) rule tokens =
  let rec loop acc tl =
    let* (v, tl) = rule m tl in
    match v with
      | Some v -> loop (v :: acc) tl
      | None -> Ok (List.rev acc, tl) in
  loop [] tokens

let parse_block rule tokens =
  let parse_entries m tokens =
    let rec loop acc allow_semi tokens =
      let (sep, tl) = match tokens () with
        | Cons ((SEMI, p, f) as sep, tl) when allow_semi && obeys_alignment m p f -> ([sep], tl)
        | v -> ([], fun () -> v) in
      let* (e, tl) = rule m tl in
      match e with
        | Some e -> loop (e :: acc) true tl
        | None -> Ok (List.rev acc, unfetch_tokens sep tl) in
    loop [] false tokens in

  match tokens () with
    | Cons ((LCURLY, _, _), tl) ->
      let* (acc, tl) = parse_entries ~-1 tl in
      let* (_, tl) = expect_tok RCURLY tl "missing '}'" in
      Ok (acc, tl)
    | Cons ((_, p, _), _) as v -> parse_entries p.colno (fun () -> v)
    | _ -> Error (dummy_pos, "missing aligned block")

let parse_cseq ?(sep = COMMA) ?(m = ~-1) rule tokens err =
  (* unlike when parsed inline, we can't rely on the closing parenthesis or
   * the like to decide if we've reached the end of the sequence *)
  let* (e, tl) = rule m tokens in
  match e with
    | None -> Ok ([], tl)
    | Some e ->
      let rec loop acc tl =
        let (delimed, tl) = maybe_tok ~m sep tl in
        if delimed then
          let* (e, tl) = expect_rule (rule m) tl err in
          loop (e :: acc) tl
        else Ok (List.rev acc, tl) in
      loop [e] tl

let parse_many_idvars ?(m = ~-1) tokens =
  let rec loop acc tl =
    match tl () with
      | Cons ((IDVAR n, p, f), tl) when obeys_alignment m p f -> loop (n :: acc) tl
      | v -> (List.rev acc, fun () -> v) in
  loop [] tokens

let parse_infix ?(m = ~-1) op_table rule tokens err =
  let rec climb_prec lhs prec m tokens =
    match tokens () with
      | Cons ((OPSEQ op, p, f), tl) as v when obeys_alignment m p f -> begin
        match op_table op with
          | None -> Ok (lhs, fun () -> v)
          | Some (lhs_prec, rhs_prec, combinef) ->
            if prec >= lhs_prec then Ok (lhs, fun () -> v)
            else begin
              let* (rhs, tl) = expect_rule (rule m) tl err in
              let* (rhs, tl) = climb_prec rhs rhs_prec m tl in
              climb_prec (combinef op lhs rhs) prec m tl
            end
      end
      | v -> Ok (lhs, fun () -> v) in

  let* (lhs, tl) = rule m tokens in
  match lhs with
    | None -> Ok (None, tl)
    | Some lhs ->
      let* (res, tl) = climb_prec lhs 0 m tl in
      Ok (Some res, tl)

let dump_tokens tokens =
  let iterf (tok, p, _) =
    printf "(%d, %d) %a\n" (p.lineno + 1) (p.colno + 1) output_token tok in
  Seq.iter iterf tokens

let default_prec_table = function
  | "=" -> Some (1, 0)
  | "||" -> Some (2, 2)
  | "&&" -> Some (3, 3)
  | "<<" | ">>" -> Some (8, 8)
  | op ->
    match op.[0] with
      | '!' | '=' | '<' | '>' -> Some (4, 4)
      | '@' -> Some (5, 4)
      | ':' -> Some (6, 5)
      | '+' | '-' | '|' | '^' -> Some (7, 7)
      | '*' | '/' | '%' | '&' -> Some (8, 8)
      | _ -> None

let rec prog tokens =
  parse_block toplevel tokens

and toplevel m tokens =
  match tokens () with
    | Cons ((DEF, p, f), tl) when obeys_alignment m p f ->
      let* (vb, tl) = expect_some (parse_block binding) tl "missing bindings" in
      Ok (Some (TopDef vb), tl)
    | Cons ((EXTERN, p, f), tl) when obeys_alignment m p f ->
      let* (vb, tl) = expect_some (parse_block extern_def) tl "missing external definitions" in
      Ok (Some (TopExtern vb), tl)
    | Cons ((TYPE, p, f), tl) when obeys_alignment m p f ->
      let* (vb, tl) = expect_some (parse_block type_alias) tl "missing type aliases" in
      Ok (Some (TopAlias vb), tl)
    | Cons ((DATA, p, f), tl) when obeys_alignment m p f ->
      let* (vb, tl) = expect_some (parse_block data_def) tl "missing data definitions" in
      Ok (Some (TopData vb), tl)
(*
    | Cons ((TRAIT, p, f), tl) when obeys_alignment m p f ->
    | Cons ((IMPL, p, f), tl) when obeys_alignment m p f ->
*)
    | v ->
      let* (e, tl) = expr m (fun () -> v) in
      Ok (Option.map (fun e -> TopExpr e) e, tl)

and extern_def m tokens =
  match tokens () with
    | Cons ((IDVAR n, p, f), tl) when obeys_alignment m p f -> begin
      (* setup the alignment to be just after the variable *)
      let m = if m = ~-1 then m else m + 1 in
      let* (_, tl) = expect_tok ~m COLON tl "missing ':'" in
      let* (annot, tl) = expect_rule (annot m) tl "missing type annotation" in
      let* (_, tl) = expect_tok ~m (OPSEQ "=") tl "missing '='" in
      match tl () with
        | Cons ((STR extname, p, f), tl) when obeys_alignment m p f ->
          Ok (Some (n, annot, extname), tl)
        | Cons ((_, p, _), _) -> Error (p, "missing external definition name")
        | _ -> Error (dummy_pos, "missing external definition name")
    end
    | v -> Ok (None, fun () -> v)

and type_alias m tokens =
  match tokens () with
    | Cons ((IDCTOR n, p, f), tl) when obeys_alignment m p f ->
      (* setup the alignment to be just after the variable *)
      let m = if m = ~-1 then m else m + 1 in
      let (args, tl) = parse_many_idvars ~m tl in
      let* (_, tl) = expect_tok ~m (OPSEQ "=") tl "missing '='" in
      let* (annot, tl) = expect_rule (annot m) tl "missing type annotation" in
      Ok (Some (n, args, annot), tl)
    | v -> Ok (None, fun () -> v)

and data_def m tokens =
  match tokens () with
    | Cons ((IDCTOR n, p, f), tl) when obeys_alignment m p f -> begin
      (* setup the alignment to be just after the variable *)
      let m = if m = ~-1 then m else m + 1 in
      let (args, tl) = parse_many_idvars ~m tl in
      let* (_, tl) = expect_tok ~m (OPSEQ "=") tl "missing '='" in
      let* (ctors, tl) = parse_cseq ~sep:(OPSEQ "|") ~m ctor_def tl "missing data constructor" in
      if ctors = [] then
        let (p, _) = peek_position tl in
        Error (p, "missing data constructor")
      else Ok (Some (n, args, ctors), tl)
    end
    | v -> Ok (None, fun () -> v)

and ctor_def m tokens =
  match fetch_tokens 3 tokens with
    | ((LPAREN, p, f) :: (OPSEQ op, q, _) :: (RPAREN, _, _) :: xs, tl) when obeys_alignment m p f ->
      if op.[0] = ':' then
        let tl = unfetch_tokens xs tl in
        let* (args, tl) = parse_many ~m annot3 tl in
        Ok (Some ("(" ^ op ^ ")", args), tl)
      else Error (q, "This operator can only be used to name values")
    | ((IDCTOR n, p, f) :: xs, tl) when obeys_alignment m p f ->
      let tl = unfetch_tokens xs tl in
      let* (args, tl) = parse_many ~m annot3 tl in
      Ok (Some (n, args), tl)
    | (xs, tl) -> Ok (None, unfetch_tokens xs tl)

and expr m tokens =
  let* (e, tl) = expr2_infix m tokens in
  match e with
    | Some e ->
      let (found, tl) = maybe_tok ~m COLON tl in
      if found then
        let* (annot, tl) = expect_rule (annot m) tl "missing type annotation" in
        Ok (Some (ExprTyped (e, annot)), tl)
      else Ok (Some e, tl)
    | t -> Ok (t, tl)

and expr2_infix m tokens =
  let op_table op =
    let combinef op l r =
      if op.[0] = ':' then Ast.Cons ("(" ^ op ^ ")", [l; r]) else Binary (op, l, r) in
    let n =
      if op.[0] = ':' then String.sub op 1 (String.length op - 1) else op in
    default_prec_table n |> Option.map (fun (l, r) -> (l, r, combinef)) in

  parse_infix ~m op_table expr2_prefix tokens "missing expression after infix operator"

and expr2_prefix m tokens =
  let map_prefix = function
  (* these operators ONLY exists for value variants and are remapped here *)
    | "!" | "-" as op -> Some op
    | op ->
      (* these ones follow the usual rule of : being for ctors *)
      if op.[0] = '~' then Some op
      else if op.[0] = ':' && op.[1] = '~' then Some ("(" ^ op ^ ")")
      else None in

  let rec loop acc tl =
    let tail tl =
      let* (e, tl) = expr3 m tl in
      match e with
        | Some e ->
          let foldf e op =
            if op.[0] = '(' then Ast.Cons (op, [e]) else Unary (op, e) in
          Ok (Some (List.fold_left foldf e acc), tl)
        | None ->
          if acc = [] then Ok (None, tl)
          else
            let (p, _) = peek_position tl in
            Error (p, "misssing expression after prefix operator") in
    match tl () with
      | Cons ((OPSEQ op, p, f), tl) as v when obeys_alignment m p f -> begin
        match map_prefix op with
          | Some op -> loop (op :: acc) tl
          | None -> tail (fun () -> v)
      end
      | v -> tail (fun () -> v) in
  loop [] tokens

and expr3 m tokens =
  (* generally ((Ctor) x y) will promote textual named data constructor into a
   * function first, making it definitely NOT a syntactic value.
   * (Ctor x y) on the other hand (assume saturated) CAN be a syntactic value.
   * (Note: "ref" is never syntactic, so we don't have to handle it here *)
  match fetch_tokens 3 tokens with
    | ((LPAREN, p, f) :: (OPSEQ op, _, _) :: (RPAREN, _, _) :: xs, tl)
      when op.[0] = ':' && obeys_alignment m p f ->
      let* (args, tl) = parse_many ~m expr4 (unfetch_tokens xs tl) in
      Ok (Some (Ast.Cons ("(" ^ op ^ ")", args)), tl)
    | ((IDCTOR k, p, f) :: xs, tl) when obeys_alignment m p f ->
      let* (args, tl) = parse_many ~m expr4 (unfetch_tokens xs tl) in
      Ok (Some (Ast.Cons (k, args)), tl)
    | (xs, tl) ->
      let* (f, tl) = expr4 m (unfetch_tokens xs tl) in
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
    | Cons ((IDCTOR v, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Ast.Cons (v, [])), tl)
    | Cons ((REF, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Ast.Cons ("ref", [])), tl)
    | Cons ((STR s, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Lit (LitStr s)), tl)
    | Cons ((INT z, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Lit (LitInt z)), tl)
    | Cons ((CHAR z, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Lit (LitChar z)), tl)
    | Cons ((LCURLY, p, f), _) as v when obeys_alignment m p f ->
      let* (seq, tl) = parse_block expr (fun () -> v) in
      Ok (Some (Seq seq), tl)
    | Cons ((LSQUARE, p, f), tl) when obeys_alignment m p f ->
      let* (xs, tl) = parse_cseq expr tl "missing expression" in
      let* (_, tl) = expect_tok RSQUARE tl "unclosed list expression" in
      Ok (Some (List xs), tl)
    | Cons ((LPAREN, p, f), tl) when obeys_alignment m p f -> begin
      (* parenthesized expressions are free-form *)
      match fetch_tokens 2 tl with
        | ((OPSEQ op, _, _) :: (RPAREN, _, _) :: xs, tl) ->
          let tl = unfetch_tokens xs tl in
          let name = "(" ^ op ^ ")" in
          if op.[0] = ':' then Ok (Some (Ast.Cons (name, [])), tl)
          else Ok (Some (Var name), tl)
        | (xs, tl) ->
          let tl = unfetch_tokens xs tl in
          let* (xs, tl) = parse_cseq expr tl "missing expression" in
          let* (_, tl) = expect_tok RPAREN tl "unclosed parenthesized expression" in
          match xs with
            | [x] -> Ok (Some x, tl)
            | xs -> Ok (Some (Tup xs), tl)
    end
    | Cons ((IF, p, f), tl) when obeys_alignment m p f ->
      let* (k, tl) = expect_rule (expr ~-1) tl "missing condition" in
      let* (_, tl) = expect_tok THEN tl "missing 'then'" in
      let* (t, tl) = expect_rule (expr ~-1) tl "missing 'then' clause" in
      let* (_, tl) = expect_tok ELSE tl "missing 'else'" in
      let* (f, tl) = expect_rule (expr m) tl "missing 'else' clause" in
      Ok (Some (Cond (k, t, f)), tl)
    | Cons ((LET, p, f), tl) when obeys_alignment m p f ->
      let (recur, tl) = maybe_tok REC tl in
      let* (vb, tl) = expect_some (parse_block binding) tl "missing bindings" in
      let* (_, tl) = expect_tok IN tl "missing 'in'" in
      let* (e, tl) = expect_rule (expr m) tl "missing body" in
      Ok (Some (if recur then LetRec (vb, e) else Let (vb, e)), tl)
    | Cons ((MATCH, p, f), tl) when obeys_alignment m p f ->
      let* (s, tl) = expect_rule (expr ~-1) tl "missing scrutinee" in
      let* (_, tl) = expect_tok WITH tl "missing 'with'" in
      let* (cases, tl) = expect_some (parse_block case) tl "missing cases" in
      Ok (Some (Case (s, cases)), tl)
    | Cons ((SLASH, p, f), tl) when obeys_alignment m p f ->
      let (found, tl) = maybe_tok MATCH tl in
      if found then begin
        (* we have a LamCase node of (\match p1 -> e1; ...) *)
        let* (cases, tl) = expect_some (parse_block case) tl "missing cases" in
        Ok (Some (LamCase cases), tl)
      end else begin
        (* we have a Lam node of (\p... -> e) *)
        let* (args, tl) = expect_some (parse_many pat4) tl "missing argument pattern" in
        let* (_, tl) = expect_tok ARROW tl "missing '->'" in
        let* (e, tl) = expect_rule (expr m) tl "missing expression" in
        Ok (Some (Lam (args, e)), tl)
      end

    | v -> Ok (None, fun () -> v)

and binding m tokens =
  let tail n m tl =
    (* setup the alignment to be just after the variable *)
    let m = if m = ~-1 then m else m + 1 in
    let (found, tl) = maybe_tok ~m COLON tl in
    if found then begin
      let* (annot, tl) = expect_rule (annot m) tl "missing type annotation" in
      Ok (Some (DefAnnot (n, annot)), tl)
    end else begin
      let* (args, tl) = parse_many ~m pat4 tl in
      let* (_, tl) = expect_tok ~m (OPSEQ "=") tl "missing '='" in
      let* (e, tl) = expect_rule (expr m) tl "missing initializer" in
      Ok (Some (DefValue (n, args, e)), tl)
    end in

  match fetch_tokens 3 tokens with
    | ((LPAREN, p, f) :: (OPSEQ op, q, _) :: (RPAREN, _, _) :: xs, tl) when obeys_alignment m p f ->
      if op.[0] = ':' then
        Error (q, "This operator can only be used to name data constructors")
      else
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
  let* (p, tl) = pat2_infix m tokens in
  match p with
    | Some p ->
      let (found, tl) = maybe_tok ~m COLON tl in
      if found then
        let* (annot, tl) = expect_rule (annot m) tl "missing type annotation" in
        Ok (Some (PatternTyped (p, annot)), tl)
      else Ok (Some p, tl)
    | t -> Ok (t, tl)

and pat2_infix m tokens =
  let op_table op =
    if op.[0] <> ':' then
      (* only | is allowed (used for alternation) *)
      if op = "|" then Some (1, 0, fun _ l r -> Alternate (l, r)) else None
    else
      let combinef op l r = Decons ("(" ^ op ^ ")", [l; r]) in
      let n = String.sub op 1 (String.length op - 1) in
      default_prec_table n |> Option.map (fun (l, r) -> (l + 1, r + 1, combinef)) in

  parse_infix ~m op_table pat3 tokens "missing pattern after infix operator"

and pat3 m tokens =
  (* if we wanted to exactly match the expression grammar, then the prefix (-)
   * would need to be on a separate prec level. but since this operator is
   * always integer negation, the prec level does not matter (since any other
   * parse would not result in a constant integer).
   *
   * similar thing happens with custom operators that represent ctors *)
  let fetch_args k xs tl =
    let tl = unfetch_tokens xs tl in
    let* (args, tl) = parse_many ~m pat4 tl in
    Ok (Some (Decons (k, args)), tl) in
  match fetch_tokens 3 tokens with
    | ((LPAREN, p, f) :: (OPSEQ op, q, _) :: (RPAREN, _, _) :: xs, tl) when obeys_alignment m p f ->
      if op.[0] = ':' then fetch_args ("(" ^ op ^ ")") xs tl
      else Error (q, "This operator can only be used to name values")
    | ((IDCTOR k, p, f) :: xs, tl) when obeys_alignment m p f ->
      fetch_args k xs tl
    | ((REF, p, f) :: xs, tl) when obeys_alignment m p f ->
      fetch_args "ref" xs tl
    | ((OPSEQ "-", p, f) :: xs, tl) when obeys_alignment m p f -> begin
      let tl = unfetch_tokens xs tl in
      let* (z, tl) = expect_rule (pat4 m) tl "missing pattern after integer negation" in
      match z with
        | Match (LitInt z) -> Ok (Some (Match (LitInt (Z.neg z))), tl)
        | _ -> Error (p, "expected constant integer after integer negation")
    end
    | (xs, tl) -> pat4 m (unfetch_tokens xs tl)

and pat4 m tokens =
  match tokens () with
    | Cons ((UNDERSCORE, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Cap None), tl)
    | Cons ((IDVAR n, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Cap (Some n)), tl)
    | Cons ((IDCTOR k, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Decons (k, [])), tl)
    | Cons ((REF, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Decons ("ref", [])), tl)
    | Cons ((STR s, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Match (LitStr s)), tl)
    | Cons ((INT z, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Match (LitInt z)), tl)
    | Cons ((CHAR z, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (Match (LitChar z)), tl)
    | Cons ((LSQUARE, p, f), tl) when obeys_alignment m p f ->
      let* (xs, tl) = parse_cseq pat tl "missing pattern" in
      let* (_, tl) = expect_tok RSQUARE tl "unclosed list pattern" in
      Ok (Some (Delist xs), tl)
    | Cons ((LPAREN, p, f), tl) when obeys_alignment m p f -> begin
      let* (xs, tl) = parse_cseq pat tl "missing pattern" in
      let* (_, tl) = expect_tok RPAREN tl "unclosed parenthesized pattern" in
      match xs with
        | [x] -> Ok (Some x, tl)
        | xs -> Ok (Some (Detup xs), tl)
    end

    | v -> Ok (None, fun () -> v)

and annot m tokens =
  let* (a, tl) = annot2 m tokens in
  match a with
    | Some a ->
      let (found, tl) = maybe_tok ARROW tl in
      if found then
        let* (r, tl) = expect_rule (annot m) tl "missing return type" in
        Ok (Some (TypeApp (TypeApp (TypeCtor "(->)", a), r)), tl)
      else Ok (Some a, tl)
    | t -> Ok (t, tl)

and annot2 m tokens =
  let* (f, tl) = annot3 m tokens in
  match f with
    | Some f ->
      let rec loop acc tl =
        let* (e, tl) = annot3 m tl in
        match e with
          | Some e -> loop (TypeApp (acc, e)) tl
          | None -> Ok (Some acc, tl) in
      loop f tl
    | t -> Ok (t, tl)

and annot3 m tokens =
  match tokens () with
    | Cons ((UNDERSCORE, p, f), tl) when obeys_alignment m p f ->
      Ok (Some TypeIgn, tl)
    | Cons ((IDVAR n, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (TypeVar n), tl)
    | Cons ((IDCTOR k, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (TypeCtor k), tl)
    | Cons ((REF, p, f), tl) when obeys_alignment m p f ->
      Ok (Some (TypeCtor "ref"), tl)
    | Cons ((LSQUARE, p, f), tl) when obeys_alignment m p f -> begin
      let* (e, tl) = annot ~-1 tl in
      let* (_, tl) = expect_tok RSQUARE tl "unclosed list type" in
      match e with
        | Some e -> Ok (Some (TypeApp (TypeCtor "[]", e)), tl)
        | None -> Ok (Some (TypeCtor "[]"), tl)
    end
    | Cons ((LPAREN, p, f), tl) when obeys_alignment m p f -> begin
      match fetch_tokens 2 tl with
        | ((ARROW, _, _) :: (RPAREN, _, _) :: xs, tl) ->
          Ok (Some (TypeCtor "(->)"), unfetch_tokens xs tl)
        | (xs, tl) ->
          let tl = unfetch_tokens xs tl in
          let* (xs, tl) = parse_cseq annot tl "missing type" in
          let* (_, tl) = expect_tok RPAREN tl "unclosed parenthesized type" in
          match xs with
            | [x] -> Ok (Some x, tl)
            | xs -> Ok (Some (TypeTup xs), tl)
    end

    | v -> Ok (None, fun () -> v)