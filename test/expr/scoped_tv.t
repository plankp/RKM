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
