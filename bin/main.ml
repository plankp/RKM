open Rkm
open Rkm.Lexer

let configure () =
  (* TODO: do more sophisticated arg parsing *)
  if Array.length Sys.argv <> 2 then
    failwith "Missing file name"
  else
    match Sys.argv.(1) with
      | "-" -> stdin
      | fname -> open_in_bin fname

let print_error ((pos, msg) : Lexer.srcpos * string) =
  Printf.printf "At (%lu, %lu): %s\n" pos.lineno pos.colno msg

let print_token ((pos, lexeme) : Lexer.srcpos * Lexer.lexeme) =
  Printf.printf "(%lu, %lu) " pos.lineno pos.colno;
  match lexeme with
    | Fixed t -> Printf.printf "Fixed %s\n" t
    | Ctor t -> Printf.printf "Ctor %s\n" t
    | Ident t -> Printf.printf "Ident %s\n" t
    | IntLit t -> Printf.printf "IntLit %a\n" Z.output t
    | StrLit t -> Printf.printf "StrLit %S\n" t
    | ChrLit t -> Printf.printf "ChrLit %04X\n" (Uchar.to_int t)
    | Eof -> print_endline "Eof"

let () =
  let handle = configure () in
  let (errors, tokens) = Lexer.init_state
    |> Lexer.lex (Stream.of_channel handle)
    |> Lexer.to_result in
  if errors <> [] then
    List.iter print_error errors
  else
    List.iter print_token tokens
