Unlike before, due to the unification of data and type declaration syntax,
they are both recursive
  $ GenKind << "EOF"
  > type Seq a = () -> Node a
  >      Node a = { Nil; Cons a (Seq a) }
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  Int = Int : *
  Node = Node : * -> *
  Seq = (\a. () -> Node a) : * -> *
  String = String : *
  [] = [] : * -> *
  ref = ref : * -> *

  $ GenKind << "EOF"
  > type Node a = { Nil; Cons a (Seq a) }
  >      Seq a = () -> Node a
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  Int = Int : *
  Node = Node : * -> *
  Seq = (\a$2. () -> Node a$2) : * -> *
  String = String : *
  [] = [] : * -> *
  ref = ref : * -> *
