Each case is a separate lexical scope, hence type variable a is allowed to
bind to an Int in the first case and String in the second case
  $ GenExpr << "EOF"
  > match (1, "") with
  >   (x : a, y) -> (y, x : a)
  >   (x, y : a) -> (y : a, x)
  > EOF
  match (1, "") with { (($0 : Int), ($1 : String)) -> let (x : Int) = ($0 : Int) in let (y : String) = ($1 : String) in ((y : String), (x : Int)); }
  : (String, Int)

This does not type check because both a's refer to the same type variable
  $ GenExpr << "EOF"
  > match (1, "") with (x : a, y : a) -> (y, x)
  > EOF
  Error: Cannot unify unrelated types Int and String

Basically patterns can bind fresh type variables
  $ GenExpr << "EOF"
  > \match (x : a, y) -> (y, x : a)
  >        (x, y : a) -> (y : a, x)
  > EOF
  \($0 : (a$6, a$12)) -> match ($0 : (a$6, a$12)) with { (($1 : a$6), ($2 : a$12)) -> let (x : a$6) = ($1 : a$6) in let (y : a$12) = ($2 : a$12) in ((y : a$12), (x : a$6)); }
  : (a$6, a$12) -> (a$12, a$6)

  $ GenExpr << "EOF"
  > \match (x : a, y : a) -> (y, x)
  > EOF
  \($0 : (a$6, a$6)) -> match ($0 : (a$6, a$6)) with { (($1 : a$6), ($2 : a$6)) -> let (x : a$6) = ($1 : a$6) in let (y : a$6) = ($2 : a$6) in ((y : a$6), (x : a$6)); }
  : (a$6, a$6) -> (a$6, a$6)

  $ GenExpr << "EOF"
  > \(x : a) (y : a) -> (x, y)
  > EOF
  \($0 : a$5) -> \($1 : a$5) -> let (y : a$5) = ($1 : a$5) in let (x : a$5) = ($0 : a$5) in ((x : a$5), (y : a$5))
  : a$5 -> a$5 -> (a$5, a$5)

  $ GenExpr << "EOF"
  > \(x : a) y -> (x, y : a)
  > EOF
  \($0 : a$5) -> \($1 : a$5) -> let (y : a$5) = ($1 : a$5) in let (x : a$5) = ($0 : a$5) in ((x : a$5), (y : a$5))
  : a$5 -> a$5 -> (a$5, a$5)

Note that since type variables are weak and not rigid, in this case, both a b
refer to the same type
  $ GenExpr << "EOF"
  > \(x : a) (y : b) -> (x, y : a)
  > EOF
  \($0 : b$6) -> \($1 : b$6) -> let (y : b$6) = ($1 : b$6) in let (x : b$6) = ($0 : b$6) in ((x : b$6), (y : b$6))
  : b$6 -> b$6 -> (b$6, b$6)

Not all expression contexts are allowed to bind fresh type variables
(See discussion on let bindings in generalize.t)
  $ GenExpr << "EOF"
  > 10 : a
  > EOF
  Error: unknown type variable named a

Underscore types are allowed in pattern contexts
  $ GenExpr << "EOF"
  > match [1] with [x : _] -> x
  > EOF
  match (::) 1 [] with { (::) ($0 : Int) ($1 : [Int]) -> match ($1 : [Int]) with { (::) ($2 : Int) ($3 : [Int]) -> (Raise# UNHANDLED PATTERN); [] -> let (x : Int) = ($0 : Int) in (x : Int); }; [] -> (Raise# UNHANDLED PATTERN); }
  : Int

Underscore types are also allowed in expression contexts
  $ GenExpr << "EOF"
  > (1, "") : (_, String)
  > EOF
  (1, "")
  : (Int, String)
