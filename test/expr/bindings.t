  $ GenExpr << "EOF"
  > let a : Int in ()
  > EOF
  Error: missing implementation for a

  $ GenExpr << "EOF"
  > let a : Int; a = 10; a : Int in ()
  > EOF
  Error: duplicate type annotation for a

  $ GenExpr << "EOF"
  > let a = 10; a = 10 in ()
  > EOF
  Error: duplicate definition for a

  $ GenExpr << "EOF"
  > let f True = 1; f = \_ -> 0 in ()
  > EOF
  Error: duplicate definition for f

  $ GenExpr << "EOF"
  > let f = \False -> 0; f True = 1 in ()
  > EOF
  Error: argument length mismatch for f

  $ GenExpr << "EOF"
  > let a = a in ()
  > EOF
  Error: unknown binding named a

  $ GenExpr << "EOF"
  > let a = () in a
  > EOF
  let (a$1 : ()) = () in let (a : ()) = (a$1 : ()) in (a : ())
  : ()

  $ GenExpr << "EOF"
  > let a : (); a = () in a
  > EOF
  let (a$1 : ()) = () in let (a : ()) = (a$1 : ()) in (a : ())
  : ()

  $ GenExpr << "EOF"
  > let x = 1; y = 2 in let x = y; y = x in (x, y)
  > EOF
  let (x$1 : Int) = 1 in let (y$1 : Int) = 2 in let (x : Int) = (x$1 : Int) in let (y : Int) = (y$1 : Int) in let (x$1 : Int) = (y : Int) in let (y$1 : Int) = (x : Int) in let (x : Int) = (x$1 : Int) in let (y : Int) = (y$1 : Int) in ((x : Int), (y : Int))
  : (Int, Int)

  $ GenExpr << "EOF"
  > let (&) True True = True
  >     (&) _    _    = False
  > in True & False
  > EOF
  let ((&)$1 : Bool -> Bool -> Bool) = \($0 : Bool) -> \($1 : Bool) -> match ($0 : Bool) with { False -> (False : Bool); True -> match ($1 : Bool) with { False -> (False : Bool); True -> (True : Bool); }; } in let ((&) : Bool -> Bool -> Bool) = ((&)$1 : Bool -> Bool -> Bool) in ((&) : Bool -> Bool -> Bool) (True : Bool) (False : Bool)
  : Bool
