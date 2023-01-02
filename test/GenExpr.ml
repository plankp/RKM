open Rkm
open Lexing
open Driver
open Printf
open Sem

let () =
  let startp = { pos_fname = ""; pos_lnum = 0; pos_cnum = 0; pos_bol = 0 } in
  let lexbuf = Lexing.from_channel stdin in
  let result = parse startp Parser.Incremental.repl_expr lexbuf in
  match result with
    | Error (p, e) ->
      printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e
    | Ok ast ->
      match visit_top_expr core_tctx ast with
        | Error e -> List.iter (printf "Error: %s\n") e
        | Ok (ast, t, _) ->
          printf "%a\n: %a\n" Expr.output ast Type.output t