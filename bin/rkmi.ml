open Rkm
open Driver
open Lexing
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

let rec lookup_extf : string -> Eval.value option = function
  | "int_add#" -> Some (gen_extf_ii_i Z.add)
  | "int_sub#" -> Some (gen_extf_ii_i Z.sub)
  | "int_mul#" -> Some (gen_extf_ii_i Z.mul)
  | "int_div#" -> Some (gen_extf_ii_i Z.div)
  | "int_rem#" -> Some (gen_extf_ii_i Z.rem)
  | "int_and#" -> Some (gen_extf_ii_i Z.logand)
  | "int_xor#" -> Some (gen_extf_ii_i Z.logxor)
  | "int_or#" -> Some (gen_extf_ii_i Z.logor)
  | "int_eq#" -> Some (gen_extf_ii_b Z.equal)
  | _ -> None

and gen_extf_ii_i f =
  let open Eval in
  VExtf (fun p -> Ok (VExtf (fun q ->
    match (p, q) with
      | (VLit (LitInt p), VLit (LitInt q)) -> Ok (VLit (LitInt (f p q)))
      | _ -> Error "Type violation")))

and gen_extf_ii_b f =
  let open Eval in
  VExtf (fun p -> Ok (VExtf (fun q ->
    match (p, q) with
      | (VLit (LitInt p), VLit (LitInt q)) ->
        let k = if f p q then "True" else "False" in
        Ok (VCons (k, false, []))
      | _ -> Error "Type violation")))

let proc_toplevel verbose venv = function
  | AddTypes m ->
    if verbose then begin
      let iterf n (_, k) = printf "%s : %a\n" n Type.output k in
      StrMap.iter iterf m
    end;
    Ok venv
  | AddGlobl m -> begin
    match Eval.add_rec_def venv m with
      | Error e -> Error e
      | Ok venv ->
        if verbose then printf "(done)\n";
        Ok venv
  end
  | AddExtern m -> begin
    let rec loop next_venv seq =
      match seq () with
        | Seq.Nil ->
          if verbose then printf "(done)\n";
          Ok next_venv
        | Seq.Cons ((k, (_, n)), xs) ->
          match lookup_extf n with
            | None -> Error ("unknown external function " ^ n)
            | Some v ->
              loop (Eval.augment_env next_venv (k, Z.zero) v) xs in
    loop venv (StrMap.to_seq m)
  end
  | EvalExpr (e, t) -> begin
    match Eval.eval venv e with
      | Error e -> Error e
      | Ok v ->
        if verbose then printf "%a : %a\n" Eval.output v Type.output t;
        Ok venv
  end

let rec cont_eval_prog verbose tctx venv = function
  | Error (p, e) ->
    printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e;
    repl_loop tctx venv
  | Ok acc ->
    match visit_prog tctx acc with
      | Error e ->
        List.iter (printf "Error: %s\n") e;
        repl_loop tctx venv
      | Ok (seq, tctx) ->
        let rec loop venv = function
          | [] -> repl_loop tctx venv
          | x :: xs ->
            match proc_toplevel verbose venv x with
              | Ok venv -> loop venv xs
              | Error e ->
                printf "Error: %s\nEnvironment resetted\n" e;
                repl_loop core_context Eval.core_venv in
        loop venv seq

and repl_loop tctx venv =
  match read_input () with
    | None -> ()
    | Some (lines, _) ->
      let strlen = String.length lines in
      let init_pos = { pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0 } in
      if strlen > 0 && lines.[0] = ':' then
        let (init_pos, cmd, lines) =
          match String.index_opt lines ' ' with
            | None -> (init_pos, lines, "")
            | Some i ->
              let tail = String.sub lines (i + 1) (strlen - i - 1) in
              ({ init_pos with pos_cnum = i }, String.sub lines 0 i, tail) in
        match cmd with
          | ":q" | ":quit" -> ()
          | ":k" | ":kind" ->
            let lexbuf = Lexing.from_string ("{" ^ lines ^ "}") in
            let result = parse init_pos Parser.Incremental.repl_annot lexbuf in
            let () = match result with
              | Error (p, e) ->
                printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e
              | Ok ast ->
                match visit_top_alias tctx [Ast.DefAlias ("", [], ast)] with
                  | Error e ->
                    List.iter (printf "Error: %s\n") e
                  | Ok (m, _) ->
                    let (t, k) = StrMap.find "" m in
                    printf "%a : %a\n" Type.output t Type.output k in
            repl_loop tctx venv
          | ":t" | ":type" ->
            let lexbuf = Lexing.from_string ("{" ^ lines ^ "}") in
            let result = parse init_pos Parser.Incremental.repl_expr lexbuf in
            let () = match result with
              | Error (p, e) ->
                printf "Error (%d, %d): %s\n" (get_lineno p) (get_colno p) e
              | Ok ast ->
                match visit_top_expr tctx ast with
                  | Error e ->
                    List.iter (printf "Error: %s\n") e
                  | Ok (ast, t, _) ->
                    printf "%a\n: %a\n" Core.output ast Type.output t in
            repl_loop tctx venv
          | ":tctors" ->
            let iterf n (_, k) = printf "%s : %a\n" n Type.output k in
            StrMap.iter iterf tctx.tctors;
            repl_loop tctx venv
          | ":reset" ->
            printf "Environment resetted\n";
            repl_loop core_context Eval.core_venv
          | ":load" ->
            begin
              try
                let chan = open_in_bin lines in
                printf "loading file '%s'\n" lines;
                try
                  let lexbuf = Lexing.from_channel chan in
                  let result = parse init_pos Parser.Incremental.prog lexbuf in
                  close_in chan;
                  cont_eval_prog false tctx venv result
                with _ -> close_in_noerr chan
              with _ -> ()
            end;
            printf "cannot load file '%s'\n" lines;
            repl_loop tctx venv
          | _ ->
            printf "unknown command '%s'\n" cmd;
            repl_loop tctx venv
      else
        let lexbuf = Lexing.from_string lines in
        let result = parse init_pos Parser.Incremental.prog lexbuf in
        cont_eval_prog true tctx venv result

let () =
  repl_loop core_context Eval.core_venv