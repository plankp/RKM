open Rkm
open Driver

let () =
  let lexbuf = Lexing.from_channel stdin in
  let result = parse Parser.prog lexbuf in
  match result with
    | Error (p, e) ->
      Printf.printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
    | Ok (acc, _) -> List.iter (Printf.printf "%a\n" Ast.output_top) acc