open Rkm
open Driver
open Printf
open Sem

let read_input () =
  try
    let buf = Buffer.create 160 in
    let rec loop lineno =
      printf "%u| " lineno;
      flush stdout;

      let line = input_line stdin in
      let len = String.length line in
      if len > 0 && line.[len - 1] = '\\' then begin
        Buffer.add_substring buf line 0 (len - 1);
        Buffer.add_char buf '\n';
        loop (lineno + 1)
      end else begin
        Buffer.add_string buf line;
        Some (Buffer.contents buf, lineno + 1)
      end in
    loop 1
  with End_of_file -> None

let rec loop tctx =
  match read_input () with
    | None -> ()
    | Some (lines, _) ->
      let strlen = String.length lines in
      if strlen > 0 && lines.[0] = ':' then
        let (cmd, lines) =
          match String.index_opt lines ' ' with
            | None -> (lines, "")
            | Some i ->
              let tail = String.sub lines (i + 1) (strlen - i - 1) in
              (String.sub lines 0 i, tail) in
        match cmd with
          | ":q" | ":quit" -> ()
          | ":k" | ":kind" ->
            let lexbuf = Lexing.from_string lines in
            let result = parse (Parser.annot ~-1) lexbuf in
            let () = match result with
              | Error (p, e) ->
                printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
              | Ok (None, _) -> ()
              | Ok (Some ast, _) ->
                match visit_alias tctx ("", [], ast) with
                  | Error e ->
                    List.iter (printf "Error: %s\n") e
                  | Ok (_, t, k, _) ->
                    printf "%a : %a\n" Type.output t Type.output k in
            loop tctx
          | ":t" | ":type" ->
            let lexbuf = Lexing.from_string lines in
            let result = parse (Parser.expr ~-1) lexbuf in
            let () = match result with
              | Error (p, e) ->
                printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e
              | Ok (None, _) -> ()
              | Ok (Some ast, _) ->
                match visit_top_expr tctx ast with
                  | Error e ->
                    List.iter (printf "Error: %s\n") e
                  | Ok (ast, t, tctx) ->
                    let (ast, _) = Expr.expand_type tctx.subst ast in
                    printf "%a\n: %a\n" Expr.output ast Type.output t in
            loop tctx
          | _ ->
            printf "unknown command '%s'\n" cmd;
            loop tctx
      else begin
        let lexbuf = Lexing.from_string lines in
        let result = parse Parser.prog lexbuf in
        let tctx = match result with
          | Error (p, e) ->
            printf "Error (%d, %d): %s\n" (p.lineno + 1) (p.colno + 1) e;
            tctx
          | Ok (acc, _) ->
            match visit_prog tctx acc with
              | Error e ->
                List.iter (printf "Error: %s\n") e;
                tctx
              | Ok tctx ->
                tctx in
        loop tctx
      end

let () =
  loop core_tctx