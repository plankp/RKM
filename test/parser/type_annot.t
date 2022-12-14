  $ GenAst << "EOF"
  > let f = 10 + 20 : Int in f  // Int annotates over the summation
  > 
  > let empty = \match
  >      ([] : [] a) -> True           // [] a is the same as [a]
  >      (_ :: _ | _ : [a]) -> False   // [a] annotates over the whole pattern
  >  in empty
  > 
  > let pack (x : a) (y : a) = (x, y) in pack
  > 
  > // type annotations are aligned like initializers:
  > // they must be on the right of the binding name
  > let pack : a -> b -> (a, b)
  >     pack x y = (x, y)
  >  in pack
  > EOF
  let { f = ((10 + 20) : Int); } in f
  let { empty = (\match { ([] : ([] a)) -> True; ((((::) _ _)|_) : ([] a)) -> False; }); } in empty
  let { pack (x : a) (y : a) = (x, y); } in pack
  let { pack : (((->) a) (((->) b) (a, b))); pack x y = (x, y); } in pack
