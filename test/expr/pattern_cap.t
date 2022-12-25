We only support linear patterns, so binding a twice is not allowed
  $ GenExpr << "EOF"
  > match (1, 2) with (a, a) -> 1; _ -> 0
  > EOF
  Error: repeated capture of a

On the other hand, a binding must appear on both sides of an or-pattern
even when it's obvious it will be always match...
  $ GenExpr << "EOF"
  > match 1 with a | _ -> ()
  > EOF
  Error: binding a is only captured on one branch

or when it's obvious it will never match that case
  $ GenExpr << "EOF"
  > match 1 with _ | b -> ()
  > EOF
  Error: binding b is only captured on one branch

And to make sure you still can't bind multiple times through an or-pattern
  $ GenExpr << "EOF"
  > match (1, 2) with (a, a | a) -> 1; _ -> 0
  > EOF
  Error: repeated capture of a

Just an example of it actually working fine
  $ GenExpr << "EOF"
  > match [] with
  >   [_, _, a] -> a
  >   [_, a] -> a
  >   [a] -> a
  >   _ -> 0
  > EOF
  match [] with { (::) ($0 : Int) ($1 : [Int]) -> match ($1 : [Int]) with { (::) ($2 : Int) ($3 : [Int]) -> match ($3 : [Int]) with { (::) ($4 : Int) ($5 : [Int]) -> match ($5 : [Int]) with { (::) ($6 : Int) ($7 : [Int]) -> 0; [] -> (let (a : Int) = ($4 : Int) in (a : Int)); }; [] -> (let (a : Int) = ($2 : Int) in (a : Int)); }; [] -> (let (a : Int) = ($0 : Int) in (a : Int)); }; [] -> 0; }
  : Int
