  $ GenExpr << "EOF"
  > {
  > let (~*) : ref a -> a
  >     (~*) (ref v) = v
  >     x = ref 1 in
  >  match x = 2 with { _ -> ~*x }
  > }
  > EOF
  let (~*)$1 = \$0 -> match $0 with { ref $1 -> let v = $1 in v; } in let x$1 = (\$0 -> (ref $0 : ref Int)) 1 in let (~*) = (~*)$1 in let x = x$1 in let $0 = x.0 = 2 in (~*) x
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
  let (~*)$1 = \$0 -> match $0 with { ref $1 -> let v = $1 in v; } in let x$1 = (\$0 -> (ref $0 : ref Int)) 1 in let (~*) = (~*)$1 in let x = x$1 in let _ = x.0 = 2 in (~*) x
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
  let _ = () in 1
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
  let (~*)$1 = \$0 -> match $0 with { ref $1 -> let v = $1 in v; } in let x$1 = (\$0 -> (ref $0 : ref ([String]))) ([] : [String]) in let (~*) = (~*)$1 in let x = x$1 in let _ = x.0 = ((::) "e" ((~*) x) : [String]) in let _ = let _ = x.0 = ((::) "d" ((~*) x) : [String]) in let _ = x.0 = ((::) "c" ((~*) x) : [String]) in x.0 = ((::) "b" ((~*) x) : [String]) in let _ = x.0 = ((::) "a" ((~*) x) : [String]) in (~*) x
  : [String]
