Each case is a separate lexical scope, hence type variable a is allowed to
bind to an Int in the first case and String in the second case
  $ GenExpr << "EOF"
  > match (1, "") with
  >   (x : a, y) -> (y, x : a)
  >   (x, y : a) -> (y : a, x)
  > EOF
  match (1, "") with { (x, y) -> (y, x); (x, y) -> (y, x); }
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
  (\match { (x, y) -> (y, x); (x, y) -> (y, x); })
  : (a$5, a$10) -> (a$10, a$5)

  $ GenExpr << "EOF"
  > \match (x : a, y : a) -> (y, x)
  > EOF
  (\match { (x, y) -> (y, x); })
  : (a$5, a$5) -> (a$5, a$5)

  $ GenExpr << "EOF"
  > \(x : a) (y : a) -> (x, y)
  > EOF
  (\x y -> (x, y))
  : a$5 -> a$5 -> (a$5, a$5)

  $ GenExpr << "EOF"
  > \(x : a) y -> (x, y : a)
  > EOF
  (\x y -> (x, y))
  : a$5 -> a$5 -> (a$5, a$5)

Note that since type variables are weak and not rigid, in this case, both a b
refer to the same type
  $ GenExpr << "EOF"
  > \(x : a) (y : b) -> (x, y : a)
  > EOF
  (\x y -> (x, y))
  : b$6 -> b$6 -> (b$6, b$6)

Not all expression contexts are allowed to bind fresh type variables
  $ GenExpr << "EOF"
  > 10 : a
  > EOF
  Error: unknown type variable named a

Underscore types are allowed in pattern contexts
  $ GenExpr << "EOF"
  > match [1] with [x : _] -> x
  > EOF
  match [1] with { [x] -> x; }
  : Int

Underscore types are also allowed in expression contexts
  $ GenExpr << "EOF"
  > (1, "") : (_, String)
  > EOF
  (1, "")
  : (Int, String)
