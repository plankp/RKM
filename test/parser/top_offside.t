  $ GenAst << "EOF"
  > a b c
  > d e
  >  f
  > x
  >   y
  >   z
  > g h i
  > 
  > extern
  >   int_add : Int -> Int -> Int = "int_add#"
  >   int_sub : Int -> Int -> Int = "int_sub#"
  >   int_mul : Int -> Int -> Int = "int_mul#"
  > 
  > def int_neg = int_sub 0
  > 
  > type
  >   List = []
  >   Pair a b = (a, b)
  > 
  > type
  >   Option a =
  >     | None | Some a
  >   Either a b =
  >     | Left a
  >     | Right b
  >   Seq a = | Nil | Cons a (() -> Seq a)
  > 
  > type
  >   NotEmptyList a =
  >     | (::|) a [a]
  > 
  > 1 ::| []
  > :~ 10
  > (::|)
  > 
  > \match { (::|) head _ -> head }
  > \match { head ::| _ -> head }
  > EOF
  ((a b) c)
  ((d e) f)
  ((x y) z)
  ((g h) i)
  extern { int_add : (((->) Int) (((->) Int) Int)) = int_add#; int_sub : (((->) Int) (((->) Int) Int)) = int_sub#; int_mul : (((->) Int) (((->) Int) Int)) = int_mul#; }
  def { int_neg = (int_sub 0); }
  type { List = []; Pair a b = (a, b); }
  type { Option a = None | Some a; Either a b = Left a | Right b; Seq a = Nil | Cons a (((->) ()) (Seq a)); }
  type { NotEmptyList a = (::|) a ([] a); }
  ((::|) 1 [])
  ((:~) 10)
  (::|)
  (\match { ((::|) head _) -> head; })
  (\match { ((::|) head _) -> head; })
