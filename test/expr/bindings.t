  $ GenExpr << "EOF"
  > {let a : Int in ()}
  > EOF
  Error: missing implementation for a

  $ GenExpr << "EOF"
  > {let a : Int; a = 10; a : Int in ()}
  > EOF
  Error: duplicate type annotation for a

  $ GenExpr << "EOF"
  > {let a = 10; a = 10 in ()}
  > EOF
  Error: duplicate definition for a

  $ GenExpr << "EOF"
  > {let f True = 1; f = \_ -> 0 in ()}
  > EOF
  Error: duplicate definition for f

  $ GenExpr << "EOF"
  > {let f = \False -> 0; f True = 1 in ()}
  > EOF
  Error: argument length mismatch for f

  $ GenExpr << "EOF"
  > {let a = a in ()}
  > EOF
  Error: unknown binding named a

  $ GenExpr << "EOF"
  > {let a = () in a}
  > EOF
  let a$1 = () in let a = a$1 in a
  : ()

  $ GenExpr << "EOF"
  > {let a : (); a = () in a}
  > EOF
  let a$1 = () in let a = a$1 in a
  : ()

  $ GenExpr << "EOF"
  > {let x = 1; y = 2 in let x = y; y = x in (x, y)}
  > EOF
  let x$1 = 1 in let y$1 = 2 in let x = x$1 in let y = y$1 in let x$1 = y in let y$1 = x in let x = x$1 in let y = y$1 in (x, y)
  : (Int, Int)

  $ GenExpr << "EOF"
  > {
  > let (&) True True = True
  >     (&) _    _    = False
  > in True & False
  > }
  > EOF
  let (&)$1 = \$0 -> \$1 -> match $0 with { True -> match $1 with { True -> (True : Bool); _ -> (False : Bool); }; _ -> (False : Bool); } in let (&) = (&)$1 in (&) (True : Bool) (False : Bool)
  : Bool
