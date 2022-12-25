  $ GenExpr << "EOF"
  > 10 : (->)
  > EOF
  Error: Cannot unify unrelated types * -> * -> * and *

  $ GenExpr << "EOF"
  > 10 : Int -> Int
  > EOF
  Error: Cannot unify unrelated types Int -> Int and Int
