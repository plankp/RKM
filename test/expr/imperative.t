  $ GenExpr << "EOF"
  > let (~*) : ref a -> a
  >     (~*) (ref v) = v
  >     x = ref 1 in
  > match x = 2 with { _ -> ~*x }
  > EOF
  let ((~*)$1 : (\a$1. ref a$1 -> a$1)) = \($0 : ref $10) -> match ($0 : ref $10) with { ref ($1 : $10) -> let (v : $10) = ($1 : $10) in (v : $10); } in let (x$1 : ref Int) = (\($0 : Int) -> (ref ($0 : Int) : ref Int)) 1 in let ((~*) : (\a$1. ref a$1 -> a$1)) = ((~*)$1 : (\a$1. ref a$1 -> a$1)) in let (x : ref Int) = (x$1 : ref Int) in let ($0 : ()) = (x : ref Int).0 = 2 in ((~*) : (\a$1. ref a$1 -> a$1)) (@Int) (x : ref Int)
  : Int

  $ GenExpr << "EOF"
  > let (~*) : ref a -> a
  >     (~*) (ref v) = v
  >     x = ref 1 in
  > { x = 2
  > ; ~*x }
  > EOF
  let ((~*)$1 : (\a$1. ref a$1 -> a$1)) = \($0 : ref $10) -> match ($0 : ref $10) with { ref ($1 : $10) -> let (v : $10) = ($1 : $10) in (v : $10); } in let (x$1 : ref Int) = (\($0 : Int) -> (ref ($0 : Int) : ref Int)) 1 in let ((~*) : (\a$1. ref a$1 -> a$1)) = ((~*)$1 : (\a$1. ref a$1 -> a$1)) in let (x : ref Int) = (x$1 : ref Int) in let (_ : ()) = (x : ref Int).0 = 2 in ((~*) : (\a$1. ref a$1 -> a$1)) (@Int) (x : ref Int)
  : Int

An empty sequence is just unit (as if it was an empty pair parenthesis)
  $ GenExpr << "EOF"
  > { }
  > EOF
  ()
  : ()

And all intermediately sequenced terms must have unit type
  $ GenExpr << "EOF"
  > { 1; () }
  > EOF
  Error: Cannot unify unrelated types () and Int

  $ GenExpr << "EOF"
  > { (); 1 }
  > EOF
  let (_ : ()) = () in 1
  : Int

Just a few more to make sure it's emitting the correct stuff
  $ GenExpr << "EOF"
  > let (~*) (ref v) = v
  >     x = ref [] in
  > { x = "e" :: ~*x
  > ; { x = "d" :: ~*x
  >   ; x = "c" :: ~*x
  >   ; x = "b" :: ~*x }
  > ; x = "a" :: ~*x
  > ; ~*x }
  > EOF
  let ((~*)$1 : ref ([String]) -> [String]) = \($0 : ref ([String])) -> match ($0 : ref ([String])) with { ref ($1 : $6) -> let (v : [String]) = ($1 : [String]) in (v : [String]); } in let (x$1 : ref ([String])) = (\($0 : [String]) -> (ref ($0 : [String]) : ref ([String]))) ([] : [String]) in let ((~*) : ref ([String]) -> [String]) = ((~*)$1 : ref ([String]) -> [String]) in let (x : ref ([String])) = (x$1 : ref ([String])) in let (_ : ()) = (x : ref ([String])).0 = ((::) "e" (((~*) : ref ([String]) -> [String]) (x : ref ([String]))) : [String]) in let (_ : ()) = let (_ : ()) = (x : ref ([String])).0 = ((::) "d" (((~*) : ref ([String]) -> [String]) (x : ref ([String]))) : [String]) in let (_ : ()) = (x : ref ([String])).0 = ((::) "c" (((~*) : ref ([String]) -> [String]) (x : ref ([String]))) : [String]) in (x : ref ([String])).0 = ((::) "b" (((~*) : ref ([String]) -> [String]) (x : ref ([String]))) : [String]) in let (_ : ()) = (x : ref ([String])).0 = ((::) "a" (((~*) : ref ([String]) -> [String]) (x : ref ([String]))) : [String]) in ((~*) : ref ([String]) -> [String]) (x : ref ([String]))
  : [String]
