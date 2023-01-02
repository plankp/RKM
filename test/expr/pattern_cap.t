We only support linear patterns, so binding a twice is not allowed
  $ GenExpr << "EOF"
  > {match (1, 2) with (a, a) -> 1; _ -> 0}
  > EOF
  Error: repeated capture of a

On the other hand, a binding must appear on both sides of an or-pattern
even when it's obvious it will be always match...
  $ GenExpr << "EOF"
  > {match 1 with a | _ -> ()}
  > EOF
  Error: binding a is only captured on one branch

or when it's obvious it will never match that case
  $ GenExpr << "EOF"
  > {match 1 with _ | b -> ()}
  > EOF
  Error: binding b is only captured on one branch

And to make sure you still can't bind multiple times through an or-pattern
  $ GenExpr << "EOF"
  > {match (1, 2) with (a, a | a) -> 1; _ -> 0}
  > EOF
  Error: repeated capture of a

Just an example of it actually working fine
  $ GenExpr << "EOF"
  > {
  > match [] with
  >   [_, _, a] -> a
  >   [_, a] -> a
  >   [a] -> a
  >   _ -> 0
  > }
  > EOF
  let $0 = ([] : [Int]) in match $0 with { (::) $1 $2 -> match $2 with { (::) $3 $4 -> match $4 with { (::) $5 $6 -> match $6 with { [] -> let a = $5 in a; _ -> 0; }; [] -> let a = $3 in a; }; [] -> let a = $1 in a; }; _ -> 0; }
  : Int

Make sure scrutinee does not get duplicated (at least when it shouldn't be)
  $ GenExpr << "EOF"
  > {match (\x -> x) (\x -> x) with (a|a) -> ""}
  > EOF
  let $0 = (\$0 -> let x = $0 in x) (\$0 -> let x = $0 in x) in let a = $0 in ""
  : String

Make sure if all cases are provided, we do not emit a defaulted case
  $ GenExpr << "EOF"
  > {\match True -> "True"; False -> "False"}
  > EOF
  \$0 -> match $0 with { True -> "True"; False -> "False"; }
  : Bool -> String
