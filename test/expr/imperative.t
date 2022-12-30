  $ GenExpr << "EOF"
  > {
  > let (~*) : ref a -> a
  >     (~*) (ref v) = v
  >     x = ref 1 in
  >  match x = 2 with { _ -> ~*x }
  > }
  > EOF
  let ((~*)$1 : (\a$6. ref a$6 -> a$6)) = \ @a$6 -> \($0 : ref a$6) -> match ($0 : ref a$6) with { ref ($1 : a$6) -> let (v : a$6) = ($1 : a$6) in (v : a$6); } in let (x$1 : ref Int) = (\($0 : Int) -> (ref ($0 : Int) : ref Int)) 1 in let ((~*) : (\a$6. ref a$6 -> a$6)) = ((~*)$1 : (\a$6. ref a$6 -> a$6)) in let (x : ref Int) = (x$1 : ref Int) in let ($0 : ()) = (x : ref Int).0 = 2 in ((~*) : (\a$6. ref a$6 -> a$6)) (@Int) (x : ref Int)
  : Int

  $ GenExpr << "EOF"
  > {
  > let (~*) : ref a -> a
  >     (~*) (ref v) = v
  >     x = ref 1 in
  >  { x = 2
  >  ; ~*x }
  > }
  > EOF
  let ((~*)$1 : (\a$6. ref a$6 -> a$6)) = \ @a$6 -> \($0 : ref a$6) -> match ($0 : ref a$6) with { ref ($1 : a$6) -> let (v : a$6) = ($1 : a$6) in (v : a$6); } in let (x$1 : ref Int) = (\($0 : Int) -> (ref ($0 : Int) : ref Int)) 1 in let ((~*) : (\a$6. ref a$6 -> a$6)) = ((~*)$1 : (\a$6. ref a$6 -> a$6)) in let (x : ref Int) = (x$1 : ref Int) in let (_ : ()) = (x : ref Int).0 = 2 in ((~*) : (\a$6. ref a$6 -> a$6)) (@Int) (x : ref Int)
  : Int

An empty sequence is just unit (as if it was an empty pair parenthesis)
  $ GenExpr << "EOF"
  > {
  > { }
  > }
  > EOF
  ()
  : ()

And all intermediately sequenced terms must have unit type
  $ GenExpr << "EOF"
  > {
  > { 1; () }
  > }
  > EOF
  Error: Cannot unify unrelated types () and Int

  $ GenExpr << "EOF"
  > {
  > { (); 1 }
  > }
  > EOF
  let (_ : ()) = () in 1
  : Int

Just a few more to make sure it's emitting the correct stuff
  $ GenExpr << "EOF"
  > {
  > let (~*) (ref v) = v
  >     x = ref [] in
  >  { x = "e" :: ~*x
  >  ; { x = "d" :: ~*x
  >    ; x = "c" :: ~*x
  >    ; x = "b" :: ~*x }
  >  ; x = "a" :: ~*x
  >  ; ~*x }
  > }
  > EOF
  let ((~*)$1 : (\$12. ref $12 -> $12)) = \ @$12 -> \($0 : ref $12) -> match ($0 : ref $12) with { ref ($1 : $12) -> let (v : $12) = ($1 : $12) in (v : $12); } in let (x$1 : ref ([String])) = (\($0 : [String]) -> (ref ($0 : [String]) : ref ([String]))) ([] : [String]) in let ((~*) : (\$12. ref $12 -> $12)) = ((~*)$1 : (\$12. ref $12 -> $12)) in let (x : ref ([String])) = (x$1 : ref ([String])) in let (_ : ()) = (x : ref ([String])).0 = ((::) "e" (((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))) : [String]) in let (_ : ()) = let (_ : ()) = (x : ref ([String])).0 = ((::) "d" (((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))) : [String]) in let (_ : ()) = (x : ref ([String])).0 = ((::) "c" (((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))) : [String]) in (x : ref ([String])).0 = ((::) "b" (((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))) : [String]) in let (_ : ()) = (x : ref ([String])).0 = ((::) "a" (((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))) : [String]) in ((~*) : (\$12. ref $12 -> $12)) (@[String]) (x : ref ([String]))
  : [String]
