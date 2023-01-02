The strict nature of the language prevents certain recursive initializers.

This is allowed because it's a ctor
  $ GenExpr << "EOF"
  > {let rec x = 1 :: y; y = 2 :: x in ()}
  > EOF
  let rec { x = ((::) 1 y : [Int]) ; y = ((::) 2 x : [Int]) } in ()
  : ()

This is clearly allowed
  $ GenExpr << "EOF"
  > {let rec loop x = loop x in loop ()}
  > EOF
  let rec { loop = \$0 -> let x = $0 in loop x } in loop ()
  : $10

This is not allowed
  $ GenExpr << "EOF"
  > {let rec x = x in ()}
  > EOF
  Error: recursive binding cannot have initializer of this form
