  $ ../GenKind.exe << "EOF"
  > type Foo t = ()
  > type Bar = Foo
  > EOF
  Error: unsaturated type aliases are not allowed
