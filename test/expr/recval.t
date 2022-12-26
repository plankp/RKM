The strict nature of the language prevents certain recursive initializers.

This is allowed because it's a ctor
  $ GenExpr << "EOF"
  > let rec x = 1 :: y; y = 2 :: x in ()
  > EOF
  let rec { (x : [Int]) = (::) 1 (y : [Int]) ; (y : [Int]) = (::) 2 (x : [Int]) } in ()
  : ()

This is clearly allowed
  $ GenExpr << "EOF"
  > let rec loop x = loop x in loop ()
  > EOF
  let rec { (loop : () -> $3) = \($0 : ()) -> let (x : ()) = ($0 : ()) in (loop : () -> $3) (x : ()) } in (loop : () -> $3) ()
  : $3

This is not allowed
  $ GenExpr << "EOF"
  > let rec x = x in ()
  > EOF
  Error: Recursive binding cannot have initializer of this form
