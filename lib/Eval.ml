open Printf

module V = VarInfo

type env = value V.Map.t
and value =
  | VLit of Core.literal
  | VLam of env * V.t * Core.expr
  | VTup of value ref list
  | VCons of string * bool * value ref list (* is list or not *)
  | VCell of value option ref (* for recursive values *)
  | VExtf of (value -> (value, string) result)

let core_venv = V.Map.empty

let output ppf (v : value) =
  let rec output in_list ppf = function
    (* special list printing magic *)
    | VCons ("[]", true, []) ->
      output_string ppf (if in_list then "]" else "[]")
    | VCons ("(::)", true, [hd; tl]) ->
      output_string ppf (if in_list then ", " else "[");
      output false ppf !hd;
      output true ppf !tl;

    | VLit v -> Ast.output_lit ppf v
    | VLam _ | VExtf _ -> output_string ppf "<fun>"
    | VTup [] -> output_string ppf "()"
    | VTup (x :: xs) ->
      fprintf ppf "(%a" (output false) !x;
      List.iter (fun x -> fprintf ppf ", %a" (output false) !x) xs;
      output_string ppf ")"
    | VCons (k, _, []) -> output_string ppf k
    | VCons (k, _, xs) ->
      output_string ppf k;
      let iterf x =
        match !x with
          | VCons (_, false, _ :: _) as t -> fprintf ppf " (%a)" (output false) t
          | t -> fprintf ppf " %a" (output false) t in
      List.iter iterf xs
    | VCell v -> output in_list ppf (Option.get !v) in
  output false ppf v

let rec unwrap = function
  | VCell ({ contents = Some v } as r) ->
    let v = unwrap v in r := Some v; v
  | VCell _ -> failwith "UNDEFINED VCELL"
  | t -> t

let ( let* ) = Result.bind

let rec eval (env : env) : Core.expr -> (value, string) result = function
(* ignore type things for now *)
  | ETyLam (_, e) -> eval env e
  | EApp (p, EType _) -> eval env p

  | ELit v -> Ok (VLit v)
  | ERaise msg -> Error msg
  | ELam ((n, _), e) -> Ok (VLam (env, n, e))
  | EVar (n, _) -> Ok (V.Map.find n env)

(* these ones CAN use undefined values (due to recursive value semantics) *)
  | ETup xs ->
    let* xs = eval_ref_list env xs in
    Ok (VTup xs)
  | ECons (k, t, xs) ->
    let is_list = match t with
      | Type.TCons (TCtorVar v, _) -> v == Type.varList
      | _ -> false in
    let* xs = eval_ref_list env xs in
    Ok (VCons (k, is_list, xs))
  | ELet (NonRec (n, i), e) ->
    let* i = eval env i in
    eval (augment_env env n i) e
  | ELet (Rec vb, e) ->
    let* env = add_rec_def env vb in
    eval env e

  | EApp (p, q) -> begin
    let* p = eval env p in
    let* q = eval env q in
    match (unwrap p, unwrap q) with
      | (VExtf f, q) -> f q
      | (VLam (env, n, e), q) -> eval (V.Map.add n q env) e
      | _ -> failwith "INVALID CALL SITE"
  end
  | ESet (d, idx, s) -> begin
    let* d = eval env d in
    let* s = eval env s in
    match (unwrap d, unwrap s) with
      | ((VTup xs | VCons (_, _, xs)), s) ->
        List.nth xs idx := s;
        Ok (VTup [])
      | _ -> failwith "INVALID REFERENT SITE"
  end
  | ECase (s, cases) -> begin
    let open Core in
    let decons_helper env p s =
      List.fold_left2 (fun env p s -> augment_env env p !s) env p s in
    let rec loop = function
      | (_, (PatIgnore, e) :: _) -> eval env e
      | (VLit s, (PatLit v, e) :: _) when v = s -> eval env e
      | (VTup s, (PatUnpack p, e) :: _) ->
        eval (decons_helper env p s) e
      | (VCons (k, _, s), (PatDecons (v, p), e) :: _) when v = k ->
        eval (decons_helper env p s) e
      | (s, _ :: xs) -> loop (s, xs)
      | _ -> failwith "UNMATCHED VALUE" in
    let* s = eval env s in
    loop (unwrap s, cases)
  end
  | EType _ -> failwith "UNHANDLED NODE TO EVAL"

and eval_ref_list env list =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      let* x = eval env x in
      loop (ref x :: acc) xs in
  loop [] list

and augment_env (env : env) ((n, _) : Core.name) (v : value) =
  V.Map.add n v env

and add_rec_def (env : env) (m : (Core.name * Core.expr) list) : (env, string) result =
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