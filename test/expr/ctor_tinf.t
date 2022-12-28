This one searches the currently accessible data ctors
  $ GenExpr << "EOF"
  > \match _ :: _ -> "not-empty"
  > EOF
  \($0 : [$4]) -> match ($0 : [$4]) with { (::) ($1 : $4) ($2 : [$4]) -> "not-empty"; [] -> (Raise# UNHANDLED PATTERN); }
  : [$4] -> String

This one uses the scrutinee's type information to do the lookup
  $ GenExpr << "EOF"
  > \(x : [_]) -> match x with _ :: _ -> "not-empty"
  > EOF
  \($0 : [_$4]) -> let (x : [_$4]) = ($0 : [_$4]) in let ($0 : [_$4]) = (x : [_$4]) in match ($0 : [_$4]) with { (::) ($1 : _$4) ($2 : [_$4]) -> "not-empty"; [] -> (Raise# UNHANDLED PATTERN); }
  : [_$4] -> String

Of course, for patterns, the ctor arity must be exact
  $ GenExpr << "EOF"
  > \match (::) -> "undersaturated"
  > EOF
  Error: data constructor arity mismatch

  $ GenExpr << "EOF"
  > \match (::) a b c -> "oversaturated"
  > EOF
  Error: data constructor arity mismatch

Similar test cases for expressions (instead of patterns)
  $ GenExpr << "EOF"
  > True
  > EOF
  (True : Bool)
  : Bool

  $ GenExpr << "EOF"
  > (True : Bool)
  > EOF
  (True : Bool)
  : Bool

Unlike patterns, undersaturated ctors are promoted into functions
  $ GenExpr << "EOF"
  > (::)
  > EOF
  \($0 : $1) -> \($1 : [$1]) -> ((::) ($0 : $1) ($1 : [$1]) : [$1])
  : $1 -> [$1] -> [$1]

  $ GenExpr << "EOF"
  > (::) ""
  > EOF
  (\($0 : String) -> \($1 : [String]) -> ((::) ($0 : String) ($1 : [String]) : [String])) ""
  : [String] -> [String]

Oversaturated is definitely not allowed
  $ GenExpr << "EOF"
  > \a b c -> (::) a b c
  > EOF
  Error: data constructor arity mismatch
