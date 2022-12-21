open Rkm
open Driver

let () =
  let name = Sys.argv.(1) in
  let chan = open_in_bin name in
  let lexbuf = Lexing.from_channel chan in

  let result = parse Parser.prog lexbuf in
  close_in chan;
  match result with
    | Error (p, e) ->
      Printf.printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
    | Ok (acc, _) -> List.iter (Printf.printf "%a\n" Ast.output) acc