Each case is a separate lexical scope, hence type variable a is allowed to
bind to an Int in the first case and String in the second case
  $ GenExpr << "EOF"
  > {
  > match (1, "") with
  >   (x : a, y) -> (y, x : a)
  >   (x, y : a) -> (y : a, x)
  > }
  > EOF
  let $0 = (1, "") in match $0 with { ($1, $2) -> let x = $1 in let y = $2 in (y, x); }
  : (String, Int)

This does not type check because both a's refer to the same type variable
  $ GenExpr << "EOF"
  > {match (1, "") with (x : a, y : a) -> (y, x)}
  > EOF
  Error: Cannot unify unrelated types Int and String

Basically patterns can bind fresh type variables
  $ GenExpr << "EOF"
  > {
  > \match (x : a, y) -> (y, x : a)
  >        (x, y : a) -> (y : a, x)
  > }
  > EOF
  \$0 -> match $0 with { ($1, $2) -> let x = $1 in let y = $2 in (y, x); }
  : (a$6, a$13) -> (a$13, a$6)

  $ GenExpr << "EOF"
  > {\match (x : a, y : a) -> (y, x)}
  > EOF
  \$0 -> match $0 with { ($1, $2) -> let x = $1 in let y = $2 in (y, x); }
  : (a$6, a$6) -> (a$6, a$6)

  $ GenExpr << "EOF"
  > {\(x : a) (y : a) -> (x, y)}
  > EOF
  \$0 -> \$1 -> let y = $1 in let x = $0 in (x, y)
  : a$5 -> a$5 -> (a$5, a$5)

  $ GenExpr << "EOF"
  > {\(x : a) y -> (x, y : a)}
  > EOF
  \$0 -> \$1 -> let y = $1 in let x = $0 in (x, y)
  : a$5 -> a$5 -> (a$5, a$5)

Note that since type variables are weak and not rigid, in this case, both a b
refer to the same type
  $ GenExpr << "EOF"
  > {\(x : a) (y : b) -> (x, y : a)}
  > EOF
  \$0 -> \$1 -> let y = $1 in let x = $0 in (x, y)
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
  let $0 = ((::) 1 ([] : [Int]) : [Int]) in match $0 with { (::) $1 $2 -> match $2 with { [] -> let x = $1 in x; _ -> (Raise# UNHANDLED PATTERN); }; _ -> (Raise# UNHANDLED PATTERN); }
  : Int

Underscore types are also allowed in expression contexts
  $ GenExpr << "EOF"
  > {(1, "") : (_, String)}
  > EOF
  (1, "")
  : (Int, String)
