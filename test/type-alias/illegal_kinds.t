  $ ../GenKind.exe << "EOF"
  > type Foo x = x x
  > EOF
  Error: Cannot unify recursive types $0 and $0 -> $1

  $ ../GenKind.exe << "EOF"
  > type Foo = (->) -> Char
  > EOF
  Error: Cannot unify unrelated types * and * -> * -> *
