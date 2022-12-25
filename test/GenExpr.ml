open Rkm
open Driver
open Printf
open Sem

let () =
  let lexbuf = Lexing.from_channel stdin in
  let result = parse (Parser.expr ~-1) lexbuf in
  match result with
    | Error (p, e) ->
      printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
    | Ok (None, _) -> ()
    | Ok (Some ast, _) ->
      match visit_top_expr core_tctx ast with
        | Error e -> List.iter (printf "Error: %s\n") e
        | Ok (ast, t, tctx) ->
          let (ast, _) = Expr.expand_type tctx.subst ast in
          printf "%a\n: %a\n" Expr.output ast Type.output t
