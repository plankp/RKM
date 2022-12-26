open Printf
open Expr
open Type

type pat_matrix = (Ast.ast_pat list * expr) list
type scrut = expr * Type.t

(* purely for debugging purposes *)
let dump_pat_matrix (m : pat_matrix) =
  let iterf (p, e) =
    List.iter (printf "%a " Ast.output_pat) p;
    printf "-> (%a)\n" Expr.output e in
  print_endline "{";
  List.iter iterf m;
  print_endline "}"

let partition (lenenc : 'a list) (s : 'b list) (m : pat_matrix) =
  let rec col_wise cols action = function
    | ([], Ast.Alternate (p, q) :: xs) ->
      (* expand alternate pattern:
       * [[... (p | q) ... -> e]] becomes [[... p ... -> e]
       *                                   [... q ... -> e]] *)
      let (p, pcol) = col_wise cols action ([], p :: xs) in
      let (q, qcol) = col_wise cols action ([], q :: xs) in
      (p @ q, pcol @ qcol)
    | ([], x :: xs) -> ([x], [List.rev_append cols xs, action])
    | (_ :: ln, x :: xs) -> col_wise (x :: cols) action (ln, xs)
    | _ -> failwith "DIMENSION MISMATCH" in

  let rec row_wise pivot rows = function
    | [] -> (List.rev pivot, List.rev rows)
    | (p, a) :: xs ->
      let (p, new_rows) = col_wise [] a (lenenc, p) in
      row_wise (List.rev_append p pivot) (List.rev_append new_rows rows) xs in

  let rec loop acc = function
    | ([], x :: xs) -> (x, List.rev_append acc xs)
    | (_ :: ln, x :: xs) -> loop (x :: acc) (ln, xs)
    | _ -> failwith "DIMENSION MISMATCH" in

  let (s, rem) = loop [] (lenenc, s) in
  let (pivot, m) = row_wise [] [] m in
  (s, pivot, rem, m)

let bind name id ty init body = ELet (NonRec (((name, id), ty), init), body)

let specialize_tup (s : expr) (xs : Type.t list) (pivot : Ast.ast_pat list) (m : pat_matrix) =
  let expansion = lazy (List.map (fun _ -> Ast.Cap None) xs) in
  let foldf acc (m, a) = function
    | Ast.Detup xs ->
      (List.rev_append xs m, a) :: acc
    | Ast.Cap None ->
      (List.rev_append (Lazy.force expansion) m, a) :: acc
    | Ast.Cap (Some cap) ->
      (List.rev_append (Lazy.force expansion) m, bind cap 0L (TTup xs) s a) :: acc
    | _ -> acc in
  List.fold_left2 foldf [] m pivot |> List.rev

let specialize_var ((s, ty) : scrut) (k : string) (xs : Type.t list) (pivot : Ast.ast_pat list) (m : pat_matrix) =
  let expansion = lazy (List.map (fun _ -> Ast.Cap None) xs) in
  let foldf acc (m, a) = function
    | Ast.Decons (t, xs) when t = k ->
      (List.rev_append xs m, a) :: acc
    | Ast.Cap None ->
      (List.rev_append (Lazy.force expansion) m, a) :: acc
    | Ast.Cap (Some cap) ->
      (List.rev_append (Lazy.force expansion) m, bind cap 0L ty s a) :: acc
    | _ -> acc in
  List.fold_left2 foldf [] m pivot |> List.rev

let specialize_lit ((s, ty) : scrut) (lit : Ast.ast_lit) (pivot : Ast.ast_pat list) (m : pat_matrix) =
  let foldf acc (m, a) = function
    | Ast.Match v when v = lit -> (m, a) :: acc
    | Ast.Cap None -> (m, a) :: acc
    | Ast.Cap (Some cap) -> (m, bind cap 0L ty s a) :: acc
    | _ -> acc in
  List.fold_left2 foldf [] m pivot |> List.rev

let defaulted ((s, ty) : scrut) (pivot : Ast.ast_pat list) (m : pat_matrix) =
  let foldf acc (m, a) = function
    | Ast.Cap None -> (m, a) :: acc
    | Ast.Cap (Some cap) -> (m, bind cap 0L ty s a) :: acc
    | _ -> acc in
  List.fold_left2 foldf [] m pivot |> List.rev

let search_pivot pats =
  let rec loop acc = function
    | Ast.Cap _ as x :: xs -> loop (x :: acc) xs
    | tl -> (List.rev acc, tl) in
  loop [] pats

let rec conv (id : int64) (s : scrut list) (m : pat_matrix) =
  match m with
    | [] -> ERaise "UNHANDLED PATTERN"
    | (x, action) :: _ ->
      match search_pivot x with
        | (hd, []) -> begin
          (* first row was all wildcards, we're done *)
          let foldf action (s, ty) = function
            | Ast.Cap (Some k) -> bind k 0L ty s action
            | _ -> action in
          List.fold_left2 foldf action s hd
        end
        | (lenenc, _) ->
          let ((s, ty), pivot, rem, m) = partition lenenc s m in
          match ty with
            | TTup xs ->
              let foldf (id, rem, decons) x =
                let tmp = (("", id), x) in
                (Int64.succ id, (EVar tmp, x) :: rem, tmp :: decons) in
              let (id, rem, decons) = List.fold_left foldf (id, rem, []) xs in

              let m = specialize_tup s xs pivot m in
              ECase (s, [PatUnpack (List.rev decons), conv id rem m])

            | TCons (TCtorVar k, args) ->
              let foldf cases (k, xs) =
                let foldf (id, rem, decons) x =
                  let tmp = (("", id), x) in
                  (Int64.succ id, (EVar tmp, x) :: rem, tmp :: decons) in
                let (id, rem, decons) = List.fold_left foldf (id, rem, []) xs in

                let m = specialize_var (s, ty) k xs pivot m in
                (PatDecons (k, (List.rev decons)), conv id rem m) :: cases in
              let cases = List.fold_left foldf [] (Type.inst_variant k args) in
              ECase (s, cases)

            | TChr | TStr | TInt ->
              let listed = Hashtbl.create 32 in
              let iterf = function
                | Ast.Match lit -> Hashtbl.replace listed lit ()
                | _ -> () in
              List.iter iterf pivot;

              let foldf lit () cases =
                let m = specialize_lit (s, ty) lit pivot m in
                (PatLit lit, conv id rem m) :: cases in

              let cases = [PatIgnore, conv id rem (defaulted (s, ty) pivot m)] in
              let cases = Hashtbl.fold foldf listed cases in
              ECase (s, cases)

            | _ ->
              ECase (s, [PatIgnore, conv id rem (defaulted (s, ty) pivot m)])