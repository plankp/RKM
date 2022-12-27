open Printf

module V = VarInfo

type env = value V.Map.t
and value =
  | VLit of Expr.literal
  | VLam of env * V.t * Expr.expr
  | VTup of value list
  | VCons of string * value list
  | VCell of value option ref (* for recursive values *)
  | VExtf of (value -> (value, string) result)

let core_venv = V.Map.empty

let rec output ppf = function
  | VLit v -> Ast.output_lit ppf v
  | VLam _ | VExtf _ -> output_string ppf "<fun>"
  | VTup [] -> output_string ppf "()"
  | VTup (x :: xs) ->
    fprintf ppf "(%a" output x;
    List.iter (fprintf ppf ", %a" output) xs;
    output_string ppf ")"
  | VCons (k, []) -> output_string ppf k
  | VCons (k, xs) ->
    output_string ppf k;
    let iterf = function
      | VCons (_, _ :: _) as t -> fprintf ppf " (%a)" output t
      | t -> fprintf ppf " %a" output t in
    List.iter iterf xs
  | VCell v -> output ppf (Option.get !v)

let rec unwrap = function
  | VCell ({ contents = Some v } as r) ->
    let v = unwrap v in r := Some v; v
  | VCell _ -> failwith "UNDEFINED VCELL"
  | t -> t

let ( let* ) = Result.bind

let rec eval (env : env) : Expr.expr -> (value, string) result = function
  | ELit v -> Ok (VLit v)
  | ERaise msg -> Error msg
  | ELam ((n, _), e) -> Ok (VLam (env, n, e))
  | EVar (n, _) -> Ok (V.Map.find n env)

(* these ones CAN use undefined values (due to recursive value semantics) *)
  | ETup xs ->
    let* xs = eval_list env xs in
    Ok (VTup xs)
  | ECons (k, xs) ->
    let* xs = eval_list env xs in
    Ok (VCons (k, xs))
  | ELet (NonRec (n, i), e) ->
    let* i = eval env i in
    eval (augment_env env n i) e
  | ELet (Rec vb, e) ->
    let* env = add_rec_def env vb in
    eval env e

  | EApp (p, EType _) -> eval env p
  | EApp (p, q) -> begin
    let* p = eval env p in
    let* q = eval env q in
    match (unwrap p, unwrap q) with
      | (VExtf f, q) -> f q
      | (VLam (env, n, e), q) -> eval (V.Map.add n q env) e
      | _ -> failwith "INVALID CALL SITE"
  end
  | ECase (s, cases) -> begin
    let open Expr in
    let rec loop = function
      | (_, (PatIgnore, e) :: _) -> eval env e
      | (VLit s, (PatLit v, e) :: _) when v = s -> eval env e
      | (VTup s, (PatUnpack p, e) :: _) ->
        eval (List.fold_left2 augment_env env p s) e
      | (VCons (k, s), (PatDecons (v, p), e) :: _) when v = k ->
        eval (List.fold_left2 augment_env env p s) e
      | (s, _ :: xs) -> loop (s, xs)
      | _ -> failwith "UNMATCHED VALUE" in
    let* s = eval env s in
    loop (unwrap s, cases)
  end
  | EType _ -> failwith "UNHANDLED NODE TO EVAL"

and eval_list env list =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      let* x = eval env x in
      loop (x :: acc) xs in
  loop [] list

and augment_env (env : env) ((n, _) : Expr.name) (v : value) =
  V.Map.add n v env

and add_rec_def (env : env) (m : (Expr.name * Expr.expr) list) : (env, string) result =
  let mkcell n env = V.Map.add n (VCell (ref None)) env in
  let env = List.fold_left (fun env ((n, _), _) -> mkcell n env) env m in
  let rec loop = function
    | [] -> Ok env
    | ((n, _), i) :: xs ->
      match V.Map.find n env with
        | VCell cell ->
          let* i = eval env i in
          cell := Some i;
          loop xs
        | _ -> failwith "!?" in
  loop m