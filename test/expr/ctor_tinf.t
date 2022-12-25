This one searches the currently accessible data ctors
  $ GenExpr << "EOF"
  > \match _ :: _ -> "not-empty"
  > EOF
  (\($0 : [$3]) -> match ($0 : [$3]) with { (::) ($0 : $3) ($1 : [$3]) -> "not-empty"; [] -> (Raise# UNHANDLED PATTERN); })
  : [$3] -> String

This one uses the scrutinee's type information to do the lookup
  $ GenExpr << "EOF"
  > \(x : [_]) -> match x with _ :: _ -> "not-empty"
  > EOF
  (\($0 : [_$4]) -> (let (x : [_$4]) = ($0 : [_$4]) in match (x : [_$4]) with { (::) ($0 : _$4) ($1 : [_$4]) -> "not-empty"; [] -> (Raise# UNHANDLED PATTERN); }))
  : [_$4] -> String
