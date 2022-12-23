  $ ../GenKind.exe << "EOF"
  > type A = ()
  > type A = (A, A)
  >      B = A -> ()
  > EOF
  (->) = (->) : * -> * -> *
  A = ((), ()) : *
  B = () -> () : *
  Bool = Bool : *
  Char = Char : *
  Int = Int : *
  String = String : *
  [] = [] : * -> *
