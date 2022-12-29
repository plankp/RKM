type expr =
  | EVar of string
  | EApp of expr * expr
  | EAbs of string * expr
  | ETup of expr list
  | ELet of string * expr * expr
  | ELetA of string * Type.t * expr * expr
