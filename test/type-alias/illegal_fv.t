  $ GenKind << "EOF"
  > type A = t
  > EOF
  Error: unknown type variable named t

  $ GenKind << "EOF"
  > type A = B
  > EOF
  Error: unknown type constructor named B

  $ GenKind << "EOF"
  > type A = _
  > EOF
  Error: unnamed type not allowed in this context
