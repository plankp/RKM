The strict nature of the language prevents certain recursive initializers.

This is allowed because it's a ctor
  $ GenExpr << "EOF"
  > let rec x = 1 :: y; y = 2 :: x in ()
  > EOF
  let rec { (x : [Int]) = ((::) 1 (y : [Int]) : [Int]) ; (y : [Int]) = ((::) 2 (x : [Int]) : [Int]) } in ()
  : ()

This is clearly allowed
  $ GenExpr << "EOF"
  > let rec loop x = loop x in loop ()
  > EOF
  let rec { (loop : (\$5. (\$3. $5 -> $3))) = \($0 : $5) -> let (x : $5) = ($0 : $5) in (loop : $5 -> $3) (x : $5) } in (loop : (\$5. (\$3. $5 -> $3))) (@()) (@$8) ()
  : $8

This is not allowed
  $ GenExpr << "EOF"
  > let rec x = x in ()
  > EOF
  Error: Recursive binding cannot have initializer of this form
