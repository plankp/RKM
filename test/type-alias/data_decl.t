Things that are (clearly) illegal
  $ GenKind << "EOF"
  > data A s = A s
  >      A s = B s
  > EOF
  Error: duplicate data definition A

  $ GenKind << "EOF"
  > data A t t = A
  > EOF
  Error: duplicate type variable t

  $ GenKind << "EOF"
  > data A = A t
  > EOF
  Error: unknown type variable named t

Things that are (not so obviously) legal
  $ GenKind << "EOF"
  > data Foo = K; Bar = K
  > EOF
  (->) = (->) : * -> * -> *
  Bar = Bar : *
  Bool = Bool : *
  Char = Char : *
  Foo = Foo : *
  Int = Int : *
  String = String : *
  [] = [] : * -> *

An example of mutual recursive data definitions
  $ GenKind << "EOF"
  > data Tree a   = Empty | Node a (Forest a)
  >      Forest a = Nil | Cons (Tree a) (Forest a)
  > 
  > Cons (Node "" Nil) Nil;
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  Forest = Forest : * -> *
  Int = Int : *
  String = String : *
  Tree = Tree : * -> *
  [] = [] : * -> *

An example of some "normal" data definitions
  $ GenKind << "EOF"
  > data Option a = None | Some a
  > data Either a b = Left a | Right b
  > data NonEmptyList a = (::|) a [a]
  > 
  > 1 ::| [2, 3];
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  Either = Either : * -> * -> *
  Int = Int : *
  NonEmptyList = NonEmptyList : * -> *
  Option = Option : * -> *
  String = String : *
  [] = [] : * -> *

A series of strange kind-related test cases
  $ GenKind << "EOF"
  > data F m = F (m Int)
  > type T = F Int
  > EOF
  Error: Cannot unify unrelated types * -> * and *

  $ GenKind << "EOF"
  > data F m = F (m Int)
  > type T = F []
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  F = F : (* -> *) -> *
  Int = Int : *
  String = String : *
  T = F [] : *
  [] = [] : * -> *

  $ GenKind << "EOF"
  > data F m = F (m Int)
  > type T = F (->)
  > EOF
  Error: Cannot unify unrelated types * and * -> *

  $ GenKind << "EOF"
  > data F m = F (m Int)
  > type T = F ((->) Char)
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  F = F : (* -> *) -> *
  Int = Int : *
  String = String : *
  T = F ((->) Char) : *
  [] = [] : * -> *

And to make sure kinds are generalized correctly
  $ GenKind << "EOF"
  > data P t = P
  > type T1 = P Int
  > type T2 = P []
  > type T3 = P (->)
  > EOF
  (->) = (->) : * -> * -> *
  Bool = Bool : *
  Char = Char : *
  Int = Int : *
  P = P : (\$0. $0 -> *)
  String = String : *
  T1 = P Int : *
  T2 = P [] : *
  T3 = P (->) : *
  [] = [] : * -> *
