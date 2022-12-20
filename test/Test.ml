open Rkm
open Driver

let () =
  let lexbuf = Lexing.from_channel stdin in
  let result = parse Parser.prog lexbuf in
  match result with
    | Error e -> print_endline e
    | Ok (acc, _) -> List.iter (Printf.printf "%a\n" Ast.output) acc