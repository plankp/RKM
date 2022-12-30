  $ GenKind << "EOF"
  > type Foo x = x x
  > EOF
  Error: Cannot unify recursive types $1 and $1 -> $2

  $ GenKind << "EOF"
  > type Foo = (->) -> Char
  > EOF
  Error: Cannot unify unrelated types * and * -> * -> *
