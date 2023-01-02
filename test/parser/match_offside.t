  $ GenAst << "EOF"
  > match f
  >  g h with A -> a; B
  >            x -> b
  >           C -> c
  >            d
  >           D
  >            ->
  >            q
  > 
  > match x with { A
  >  x y -> a;
  > B -> b }
  > 
  > // gives { A; B { I; J }; C { I } }
  > match s1 with A -> a
  >               B -> match s2 with I -> i
  >                                  J -> j
  >               C -> match s2 with I -> i
  > 
  > // same as above
  > match s1 with
  >   A -> a
  >   B -> match s2 with
  >     I -> i; J -> j
  >   C ->
  >    match s2 with I -> i
  > 
  > match k with (a,
  >               b, c, d) -> (b, c, b, a)
  > 
  > \match [] -> True
  >        _ -> False
  > EOF
  match ((f g) h) with { A -> a; (B x) -> b; C -> (c d); D -> q; }
  match x with { (A x y) -> a; B -> b; }
  match s1 with { A -> a; B -> match s2 with { I -> i; J -> j; }; C -> match s2 with { I -> i; }; }
  match s1 with { A -> a; B -> match s2 with { I -> i; J -> j; }; C -> match s2 with { I -> i; }; }
  match k with { (a, b, c, d) -> (b, c, b, a); }
  (\match { [] -> True; _ -> False; })

  $ GenAst << "EOF"
  > let f x = match x with  // explicit blocks can cross an offside boundary
  >  { True -> "True"; False -> "False" } in 9
  > EOF
  let { f x = match x with { True -> "True"; False -> "False"; }; } in 9
