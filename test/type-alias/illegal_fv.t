  $ ../GenKind.exe << "EOF"
  > type A = t
  > EOF
  Error: unknown type variable named t

  $ ../GenKind.exe << "EOF"
  > type A = B
  > EOF
  Error: unknown type constructor named B
