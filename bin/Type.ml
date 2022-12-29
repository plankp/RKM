open Printf

module Name = struct
  type t = string * Z.t
  let compare = compare
end

module NameSet = Set.Make (Name)
module NameMap = Map.Make (Name)

type t =
  | TVar of string * Z.t * t option ref
  | TRigid of string * Z.t
  | TArr of t * t
  | TTup of t list
  | TPoly of string * Z.t * t

let rec unwrap_shallow = function
  | TVar (_, _, ({ contents = Some t } as r)) ->
    let t = unwrap_shallow t in r := Some t; t
  | t -> t

let rec unwrap_deep t =
  match unwrap_shallow t with
    | TArr (p, q) -> TArr (unwrap_deep p, unwrap_deep q)
    | TTup xs -> TTup (List.map unwrap_deep xs)
    | TPoly (n, id, t) -> TPoly (n, id, unwrap_deep t)
    | t -> t

let get_name = function
  | TVar (name, id, _) | TRigid (name, id) -> (name, id)
  | _ -> failwith "Invalid type to get_name on"

let unpeel_poly (t : t) =
  let rec loop acc = function
    | TPoly (n, id, t) -> loop ((n, id) :: acc) t
    | t -> (acc, t) in
  loop [] t

let rec output ppf t =
  match unwrap_shallow t with
    | TVar (name, id, _) ->
      fprintf ppf "%s.%a" name Z.output id
    | TRigid (name, id) ->
      fprintf ppf "%s.%a" name Z.output id
    | TArr (p, q) ->
      fprintf ppf "(%a -> %a)" output p output q
    | TTup [] -> output_string ppf "()"
    | TTup (x :: xs) ->
      fprintf ppf "(%a" output x;
      List.iter (fprintf ppf ", %a" output) xs;
      output_string ppf ")"
    | TPoly (n, id, t) ->
      fprintf ppf "\\%s.%a. %a" n Z.output id output t

let rec to_string t =
  match unwrap_shallow t with
    | TVar (name, id, _) ->
      sprintf "%s.%s" name (Z.to_string id)
    | TRigid (name, id) ->
      sprintf "%s.%s" name (Z.to_string id)
    | TArr (p, q) ->
      sprintf "(%s -> %s)" (to_string p) (to_string q)
    | TTup [] -> "()"
    | TTup (x :: xs) ->
      let buf = Buffer.create 64 in
      bprintf buf "(%s" (to_string x);
      List.iter (fun e -> bprintf buf ", %s" (to_string e)) xs;
      Buffer.add_string buf ")";
      Buffer.contents buf
    | TPoly (n, id, t) ->
      let buf = Buffer.create 64 in
      bprintf buf "\\%s.%s. %s" n (Z.to_string id) (to_string t);
      Buffer.contents buf

let free_tvars ?(acc = (NameSet.empty, [])) (t : t) =
  let rec loop set acc = function
    | [] -> (set, acc)
    | TRigid _ :: xs -> loop set acc xs
    | TArr (p, q) :: xs -> loop set acc (p :: q :: xs)
    | TTup ys :: xs ->
      let (set, acc) = loop set acc ys in loop set acc xs
    | TVar (_, _, { contents = Some _ }) as t :: xs ->
      loop set acc (unwrap_shallow t :: xs)
    | TVar (n, id, _) as t :: xs ->
      if NameSet.mem (n, id) set then loop set acc xs
      else loop (NameSet.add (n, id) set) (t :: acc) xs
    | TPoly (_, _, t) :: xs -> loop set acc (t :: xs) in
  let (set, acc) = acc in
  loop set acc [t]

let rec free_rigids ?(acc = NameSet.empty) (t : t) =
  let rec loop acc = function
    | [] -> acc
    | TRigid (n, id) :: xs -> loop (NameSet.add (n, id) acc) xs
    | TArr (p, q) :: xs -> loop acc (p :: q :: xs)
    | TTup ys :: xs -> loop (loop acc ys) xs
    | TVar (_, _, { contents = Some _ }) as t :: xs ->
      loop acc (unwrap_shallow t :: xs)
    | TVar _ :: xs -> loop acc xs
    | TPoly (n, id, t) :: xs ->
      let q = NameSet.remove (n, id) (free_rigids t) in
      loop (NameSet.union acc q) xs in
  loop acc [t]

let contains_tvar ((n, id) : Name.t) (t : t) =
  let rec loop = function
    | [] -> false
    | TRigid _ :: xs -> loop xs
    | TArr (p, q) :: xs -> loop (p :: q :: xs)
    | TTup ys :: xs -> if loop ys then true else loop xs
    | TVar (_, _, { contents = Some _ }) as t :: xs ->
      loop (unwrap_shallow t :: xs)
    | TVar (m, tg, _) :: xs ->
      if n = m && id = tg then true else loop xs
    | TPoly (_, _, t) :: xs -> loop (t :: xs) in
  loop [t]

let contains_rigid ((n, id) : Name.t) (t : t) =
  let rec loop = function
    | [] -> false
    | TRigid (m, tg) :: xs ->
      if n = m && id = tg then true else loop xs
    | TArr (p, q) :: xs -> loop (p :: q :: xs)
    | TTup ys :: xs -> if loop ys then true else loop xs
    | TVar (_, _, { contents = Some _ }) as t :: xs ->
      loop (unwrap_shallow t :: xs)
    | TVar _ :: xs -> loop xs
    | TPoly (m, tg, t) :: xs ->
      if m = n && tg = id then loop xs
      else loop (t :: xs) in
  loop [t]

let rec subst ?(weak = NameMap.empty) ?(rigid = NameMap.empty) = function
  | TVar (_, _, { contents = Some _ }) as t ->
    subst ~weak ~rigid (unwrap_shallow t)
  | TVar (name, id, _) as t -> begin
    match NameMap.find_opt (name, id) weak with
      | Some t -> subst ~weak ~rigid t
      | None -> t
  end
  | TRigid (name, id) as t -> begin
    match NameMap.find_opt (name, id) rigid with
      | Some t -> subst ~weak ~rigid t
      | None -> t
  end
  | TArr (p, q) ->
    TArr (subst ~weak ~rigid p, subst ~weak ~rigid q)
  | TTup xs ->
    TTup (List.map (subst ~weak ~rigid) xs)
  | TPoly (n, id, t) ->
    let rigid = NameMap.remove (n, id) rigid in
    TPoly (n, id, subst ~weak ~rigid t)