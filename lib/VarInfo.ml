module S = struct
  type t = string * Z.t
  let compare = compare
end

include S

module Map = Map.Make (S)
module Set = Set.Make (S)

let output ppf ((n, id) : t) =
  if id = Z.zero && n <> "" then output_string ppf n
  else Printf.fprintf ppf "%s$%a" n Z.output id

and to_string ((n, id) : t) =
  if id = Z.zero && n <> "" then n
  else Printf.sprintf "%s$%s" n (Z.to_string id)

let mk_fresh (n : t) (env : Set.t) : t =
  if Set.mem n env then
    let (n, _) = n in
    let rec loop id =
      if Set.mem (n, id) env then loop (Z.succ id)
      else (n, id) in
    loop Z.zero
  else n

let def_var (lift : t -> 'a) (x : t) (map : 'a Map.t) (env : Set.t) =
  if Set.mem x env then
    let y = mk_fresh x env in
    (y, Map.add x (lift y) map, Set.add y env)
  else
    (x, Map.remove x map, Set.add x env)

let def_vars (lift : t -> 'a) (xs : t list) (map : 'a Map.t) (env : Set.t) =
  let foldf (acc, map, env) x =
    let (x, map, env) = def_var lift x map env in
    (x :: acc, map, env) in
  let (xs, map, env) = List.fold_left foldf ([], map, env) xs in
  (List.rev xs, map, env)