  $ ../GenAst.exe << "EOF"
  > let x = a; y = b; g = c in z;
  > 
  > let x = a; y = b
  > in z;
  > 
  > let {x = a
  >   ; y = b} in z;
  > 
  > let x = a
  >     y = b
  >   in z;
  > 
  > let x = a; y = b c
  >     g = h
  >      i j in q;
  > 
  > let x = a; y = b c
  >     g = (h // parenthesis allows side-stepping offside rule
  >       i j) in q;
  > 
  > let rec x = a; y = b; g = c in z;
  > 
  > let rec x = a; y = b
  > in z;
  > 
  > let rec {x = a
  >   ; y = b} in z;
  > 
  > let
  > rec x = a
  >     y = b
  >   in z;
  > 
  > let rec
  >  x = a; y = b c
  >  g = h
  >    i j in q;
  > 
  > let rec
  >  x = a; y = b c
  >  g = (h // parenthesis allows side-stepping offside rule
  >  i j) in q;
  > 
  > // here we mix a match and let together
  > // (intentionally somewhat poorly formatted)
  > let rev xs = let rec loop
  >                       acc xs = match xs with
  >                         Nil -> acc
  >                         Cons x xs -> loop (cons x acc) xs
  >              in loop empty_list xs
  > in rev;
  > 
  > // operators are also allowed
  > let (++) x y = (x, y) in (p ++ q, (++) p q);
  > let (--) = \x y -> y - x in 1 -- 2;
  > EOF
  let { x = a; y = b; g = c; } in z
  let { x = a; y = b; } in z
  let { x = a; y = b; } in z
  let { x = a; y = b; } in z
  let { x = a; y = (b c); g = ((h i) j); } in q
  let { x = a; y = (b c); g = ((h i) j); } in q
  let rec { x = a; y = b; g = c; } in z
  let rec { x = a; y = b; } in z
  let rec { x = a; y = b; } in z
  let rec { x = a; y = b; } in z
  let rec { x = a; y = (b c); g = ((h i) j); } in q
  let rec { x = a; y = (b c); g = ((h i) j); } in q
  let { rev xs = let rec { loop acc xs = match xs with { Nil -> acc; (Cons x xs) -> ((loop ((cons x) acc)) xs); }; } in ((loop empty_list) xs); } in rev
  let { (++) x y = (x, y); } in ((p ++ q), (((++) p) q))
  let { (--) = (\x y -> (y - x)); } in (1 -- 2)
