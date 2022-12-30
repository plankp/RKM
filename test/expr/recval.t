The strict nature of the language prevents certain recursive initializers.

This is allowed because it's a ctor
  $ GenExpr << "EOF"
  > {let rec x = 1 :: y; y = 2 :: x in ()}
  > EOF
  let rec { (x : [Int]) = ((::) 1 (y : [Int]) : [Int]) ; (y : [Int]) = ((::) 2 (x : [Int]) : [Int]) } in ()
  : ()

This is clearly allowed
  $ GenExpr << "EOF"
  > {let rec loop x = loop x in loop ()}
  > EOF
  let rec { (loop : (\$6. (\$7. $6 -> $7))) = \ @$6 -> \ @$7 -> \($0 : $6) -> let (x : $6) = ($0 : $6) in (loop : $6 -> $7) (x : $6) } in (loop : (\$6. (\$7. $6 -> $7))) (@()) (@$10) ()
  : $10

This is not allowed
  $ GenExpr << "EOF"
  > {let rec x = x in ()}
  > EOF
  Error: recursive binding cannot have initializer of this form
