open Rkm
open Driver

let () =
  let name = Sys.argv.(1) in
  let chan = open_in_bin name in
  let lexbuf = Lexing.from_channel chan in

  let result = parse Parser.prog lexbuf in
  close_in chan;
  match result with
    | Error e -> print_endline e
    | Ok (acc, _) -> List.iter (Printf.printf "%a\n" Ast.output) acc