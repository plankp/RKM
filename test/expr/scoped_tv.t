Each case is a separate lexical scope, hence type variable a is allowed to
bind to an Int in the first case and String in the second case
  $ GenExpr << "EOF"
  > {
  > match (1, "") with
  >   (x : a, y) -> (y, x : a)
  >   (x, y : a) -> (y : a, x)
  > }
  > EOF
  let ($0 : (Int, String)) = (1, "") in match ($0 : (Int, String)) with { (($1 : Int), ($2 : String)) -> let (x : Int) = ($1 : Int) in let (y : String) = ($2 : String) in ((y : String), (x : Int)); }
  : (String, Int)

This does not type check because both a's refer to the same type variable
  $ GenExpr << "EOF"
  > {match (1, "") with (x : a, y : a) -> (y, x)}
  > EOF
  Error: Cannot unify unrelated types String and Int

Basically patterns can bind fresh type variables
  $ GenExpr << "EOF"
  > {
  > \match (x : a, y) -> (y, x : a)
  >        (x, y : a) -> (y : a, x)
  > }
  > EOF
  \($0 : (a$6, a$13)) -> match ($0 : (a$6, a$13)) with { (($1 : a$6), ($2 : a$13)) -> let (x : a$6) = ($1 : a$6) in let (y : a$13) = ($2 : a$13) in ((y : a$13), (x : a$6)); }
  : (a$6, a$13) -> (a$13, a$6)

  $ GenExpr << "EOF"
  > {\match (x : a, y : a) -> (y, x)}
  > EOF
  \($0 : (a$6, a$6)) -> match ($0 : (a$6, a$6)) with { (($1 : a$6), ($2 : a$6)) -> let (x : a$6) = ($1 : a$6) in let (y : a$6) = ($2 : a$6) in ((y : a$6), (x : a$6)); }
  : (a$6, a$6) -> (a$6, a$6)

  $ GenExpr << "EOF"
  > {\(x : a) (y : a) -> (x, y)}
  > EOF
  \($0 : a$5) -> \($1 : a$5) -> let (y : a$5) = ($1 : a$5) in let (x : a$5) = ($0 : a$5) in ((x : a$5), (y : a$5))
  : a$5 -> a$5 -> (a$5, a$5)

  $ GenExpr << "EOF"
  > {\(x : a) y -> (x, y : a)}
  > EOF
  \($0 : a$5) -> \($1 : a$5) -> let (y : a$5) = ($1 : a$5) in let (x : a$5) = ($0 : a$5) in ((x : a$5), (y : a$5))
  : a$5 -> a$5 -> (a$5, a$5)

Note that since type variables are weak and not rigid, in this case, both a b
refer to the same type
  $ GenExpr << "EOF"
  > {\(x : a) (y : b) -> (x, y : a)}
  > EOF
  \($0 : b$7) -> \($1 : b$7) -> let (y : b$7) = ($1 : b$7) in let (x : b$7) = ($0 : b$7) in ((x : b$7), (y : b$7))
  : b$7 -> b$7 -> (b$7, b$7)

Not all expression contexts are allowed to bind fresh type variables
(See discussion on let bindings in generalize.t)
  $ GenExpr << "EOF"
  > {10 : a}
  > EOF
  Error: unknown type variable named a

Underscore types are allowed in pattern contexts
  $ GenExpr << "EOF"
  > {match [1] with [x : _] -> x}
  > EOF
  let ($0 : [Int]) = ((::) 1 ([] : [Int]) : [Int]) in match ($0 : [Int]) with { (::) ($1 : Int) ($2 : [Int]) -> match ($2 : [Int]) with { [] -> let (x : Int) = ($1 : Int) in (x : Int); _ -> (Raise# UNHANDLED PATTERN); }; _ -> (Raise# UNHANDLED PATTERN); }
  : Int

Underscore types are also allowed in expression contexts
  $ GenExpr << "EOF"
  > {(1, "") : (_, String)}
  > EOF
  (1, "")
  : (Int, String)
