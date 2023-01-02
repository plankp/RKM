  $ GenKind << "EOF"
  > type A s = () -> s
  >      A s = () -> s
  > EOF
  Error: duplicate type definition A

  $ GenKind << "EOF"
  > type A t t = ()
  > EOF
  Error: duplicate type variable t
