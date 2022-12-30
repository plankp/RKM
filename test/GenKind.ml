open Rkm
open Lexing
open Driver
open Printf
open Sem

let () =
  let startp = { pos_fname = ""; pos_lnum = 0; pos_cnum = 0; pos_bol = 0 } in
  let lexbuf = Lexing.from_channel stdin in
  let result = parse startp Parser.Incremental.prog lexbuf in
  match result with
    | Error (p, e) ->
      printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e
    | Ok acc ->
      match visit_prog core_context acc with
        | Error e -> List.iter (printf "Error: %s\n") e
        | Ok (_, tctx) ->
          let iterf n (t, k) = printf "%s = %a : %a\n" n Type.output t Type.output k in
          StrMap.iter iterf tctx.tctors