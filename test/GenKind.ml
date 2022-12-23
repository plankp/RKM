open Rkm
open Driver
open Printf
open Sem

let () =
  let lexbuf = Lexing.from_channel stdin in
  let result = parse Parser.prog lexbuf in
  match result with
    | Error (p, e) ->
      printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
    | Ok (acc, _) ->
      match visit_prog core_tctx acc with
        | Error e -> List.iter (printf "Error: %s\n") e
        | Ok tctx ->
          let iterf n (t, k) = printf "%s = %a : %a\n" n Type.output t Type.output k in
          StrMap.iter iterf tctx.tctors