  $ ../GenKind.exe << "EOF"
  > type A s = () -> s
  >      A s = () -> s
  > EOF
  Error: duplicate type alias A

  $ ../GenKind.exe << "EOF"
  > type A t t = ()
  > EOF
  Error: duplicate type variable t
