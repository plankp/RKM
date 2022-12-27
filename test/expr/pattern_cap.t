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
  let ($0 : [Int]) = [] in match ($0 : [Int]) with { (::) ($1 : Int) ($2 : [Int]) -> match ($2 : [Int]) with { (::) ($3 : Int) ($4 : [Int]) -> match ($4 : [Int]) with { (::) ($5 : Int) ($6 : [Int]) -> match ($6 : [Int]) with { (::) ($7 : Int) ($8 : [Int]) -> 0; [] -> let (a : Int) = ($5 : Int) in (a : Int); }; [] -> let (a : Int) = ($3 : Int) in (a : Int); }; [] -> let (a : Int) = ($1 : Int) in (a : Int); }; [] -> 0; }
  : Int

Make sure scrutinee does not get duplicated (at least when it shouldn't be)
  $ GenExpr << "EOF"
  > match (\x -> x) (\x -> x) with (a|a) -> ""
  > EOF
  let ($0 : $8 -> $8) = (\($0 : $8 -> $8) -> let (x : $8 -> $8) = ($0 : $8 -> $8) in (x : $8 -> $8)) (\($0 : $8) -> let (x : $8) = ($0 : $8) in (x : $8)) in let (a : $8 -> $8) = ($0 : $8 -> $8) in ""
  : String
