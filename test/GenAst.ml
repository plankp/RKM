open Rkm
open Lexing
open Driver

let () =
  let startp = { pos_fname = ""; pos_lnum = 0; pos_cnum = 0; pos_bol = 0 } in
  let lexbuf = Lexing.from_channel stdin in
  let result = parse startp Parser.Incremental.prog lexbuf in
  match result with
    | Error (p, e) ->
      Printf.printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e
    | Ok acc -> List.iter (Printf.printf "%a\n" Ast.output_top) acc