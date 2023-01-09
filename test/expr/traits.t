Simple trait implementations. These are simple because the fields do not have
extra constraints: all constraints come from the implementation declaration.

Three cases: no constraints, one constraint, and more than one constraint.
  $ rkmi << "EOF"
  > extern int_eq : Int -> Int -> Bool = "int_eq#"
  > trait Eq a with \
  >   (==) : a -> a -> Bool \
  >   (!=) : a -> a -> Bool
  > 
  > impl Eq Int with \
  >   (==) a b = int_eq a b \
  >   (!=) a b = if int_eq a b then False else True
  > 
  > impl Eq a => Eq (ref a) with \
  >   (==) (ref a) (ref b) = a == b \
  >   (!=) (ref a) (ref b) = a != b
  > 
  > impl Eq a, Eq b, Eq c => Eq (a, b, c) with \
  >   (==) (a1, b1, c1) (a2, b2, c2) = a1 == a2 && b1 == b2 && c1 == c2 \
  >   (!=) (a1, b1, c1) (a2, b2, c2) = a1 != a2 || b1 != b2 || c1 != c2
  > 
  > 1 == 1
  > 1 != 1
  > ref 1 == ref 2
  > ref 1 != ref 2
  > (1, 2, ref 3) == (1, 2, ref 3)
  > (1, 2, ref 3) != (1, 2, ref 3)
  > EOF
  1| (done)
  1| 2| 3| (done)
  1| 1| 2| 3| (done)
  1| 1| 2| 3| (done)
  1| 1| 2| 3| (done)
  1| 1| True : Bool
  1| False : Bool
  1| False : Bool
  1| True : Bool
  1| True : Bool
  1| False : Bool
  1| 

Slightly more annoying case (has to do with how traits are passed around)
  $ rkmi << "EOF"
  > trait ToString a with \
  >   to_string : a -> String
  > 
  > trait Chaining a with \
  >   hmm : ToString a => a -> a
  > 
  > impl ToString String with to_string x = x
  > impl Chaining String with hmm _ = "??"
  > 
  > to_string ""
  > hmm ""
  > EOF
  1| 2| (done)
  1| 1| 2| (done)
  1| 1| (done)
  1| (done)
  1| 1| "" : String
  1| "??" : String
  1| 
