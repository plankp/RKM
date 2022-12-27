In this case, all a's refer to the same type, so we don't generalize, meaning
this example fails because a ~ Char and a ~ String is impossible
  $ GenExpr << "EOF"
  > \(x : a) -> let id : a -> a; id x = x in (id 'v', id "v")
  > EOF
  Error: Cannot unify unrelated types Char and String

In this case, a is not in the enclosing scope, and therefore, we generalize
  $ GenExpr << "EOF"
  > \x -> let id : a -> a; id x = x in (id 'v', id "v")
  > EOF
  \($0 : $3) -> let (x : $3) = ($0 : $3) in let (id$1 : (\a$4. a$4 -> a$4)) = \($0 : $10) -> let (x : $10) = ($0 : $10) in (x : $10) in let (id : (\a$4. a$4 -> a$4)) = (id$1 : (\a$4. a$4 -> a$4)) in ((id : (\a$4. a$4 -> a$4)) (@Char) '\u0076', (id : (\a$4. a$4 -> a$4)) (@String) "v")
  : $3 -> (Char, String)

As a consequence, bindings do not introduce new type variables, meaning the
following fails
  $ GenExpr << "EOF"
  > \x -> let id : a -> a; id x = x : a in ()
  > EOF
  Error: unknown type variable named a

And a nasty nasty related quantized type variables escaping their scope
  $ GenExpr << "EOF"
  > \x -> let bad : [a] -> [a]; bad xs = x :: xs in bad []
  > EOF
  Error: initializer is not general enough

Without the annotation, it does the right thing (and not generalize)
  $ GenExpr << "EOF"
  > \x -> let bad xs = x :: xs in bad []
  > EOF
  \($0 : $10) -> let (x : $10) = ($0 : $10) in let (bad$1 : [$10] -> [$10]) = \($0 : [$10]) -> let (xs : [$10]) = ($0 : [$10]) in (::) (x : $10) (xs : [$10]) in let (bad : [$10] -> [$10]) = (bad$1 : [$10] -> [$10]) in (bad : [$10] -> [$10]) []
  : $10 -> [$10]

(or generalize)
  $ GenExpr << "EOF"
  > let id x = x in (id 'a', id "z")
  > EOF
  Error: Cannot unify unrelated types Char and String

As hinted by a previous test case, we make sure the initializers are general
enough
  $ GenExpr << "EOF"
  > let p2 : a -> b -> (a, b); p2 x y = (x, y) in p2
  > EOF
  let (p2$1 : (\a$1. (\b$3. a$1 -> b$3 -> (a$1, b$3)))) = \($0 : $12) -> \($1 : $13) -> let (y : $13) = ($1 : $13) in let (x : $12) = ($0 : $12) in ((x : $12), (y : $13)) in let (p2 : (\a$1. (\b$3. a$1 -> b$3 -> (a$1, b$3)))) = (p2$1 : (\a$1. (\b$3. a$1 -> b$3 -> (a$1, b$3)))) in (p2 : (\a$1. (\b$3. a$1 -> b$3 -> (a$1, b$3)))) (@$14) (@$15)
  : $14 -> $15 -> ($14, $15)

  $ GenExpr << "EOF"
  > let p2 : a -> a -> c; p2 x y = (x, y) in p2
  > EOF
  Error: initializer is not general enough

And the identifier takes the type you provide (even if the inferred type is
more general)
  $ GenExpr << "EOF"
  > let p2 : a -> a -> (a, a); p2 x y = (x, y) in p2
  > EOF
  let (p2$1 : (\a$1. a$1 -> a$1 -> (a$1, a$1))) = \($0 : $11) -> \($1 : $12) -> let (y : $12) = ($1 : $12) in let (x : $11) = ($0 : $11) in ((x : $11), (y : $12)) in let (p2 : (\a$1. a$1 -> a$1 -> (a$1, a$1))) = (p2$1 : (\a$1. a$1 -> a$1 -> (a$1, a$1))) in (p2 : (\a$1. a$1 -> a$1 -> (a$1, a$1))) (@$13)
  : $13 -> $13 -> ($13, $13)

Underscores do work, essentially they always generalize (but they're not that
useful because you can refer to them)
  $ GenExpr << "EOF"
  > let ignore : _ -> (); ignore _ = () in (ignore 'v', ignore "v")
  > EOF
  let (ignore$1 : (\_$1. _$1 -> ())) = \($0 : $7) -> () in let (ignore : (\_$1. _$1 -> ())) = (ignore$1 : (\_$1. _$1 -> ())) in ((ignore : (\_$1. _$1 -> ())) (@Char) '\u0076', (ignore : (\_$1. _$1 -> ())) (@String) "v")
  : ((), ())

Another slight annoyance is "value restriction" which means not all things are
allowed generalize. One such example is function calls.
  $ GenExpr << "EOF"
  > let not_id = (\x -> x) (\x -> x)
  > in (not_id 'v', not_id "v")
  > EOF
  Error: Cannot unify unrelated types Char and String

We also want to make sure we can't trick it into becoming generalized!
  $ GenExpr << "EOF"
  > let not_id : a -> a
  >     not_id = (\x -> x) (\x -> x)
  > in (not_id 'v', not_id "v")
  > EOF
  Error: initializer is not general enough

The common cited workaround is to use eta-expansion
  $ GenExpr << "EOF"
  > let id : a -> a
  >     id x = (\x -> x) (\x -> x) x
  > in (id 'v', id "v")
  > EOF
  let (id$1 : (\a$1. a$1 -> a$1)) = \($0 : $15) -> let (x : $15) = ($0 : $15) in (\($0 : $15 -> $15) -> let (x : $15 -> $15) = ($0 : $15 -> $15) in (x : $15 -> $15)) (\($0 : $15) -> let (x : $15) = ($0 : $15) in (x : $15)) (x : $15) in let (id : (\a$1. a$1 -> a$1)) = (id$1 : (\a$1. a$1 -> a$1)) in ((id : (\a$1. a$1 -> a$1)) (@Char) '\u0076', (id : (\a$1. a$1 -> a$1)) (@String) "v")
  : (Char, String)

Also must examine the polymorphic recursion case. This should not type check.
  $ GenExpr << "EOF"
  > let rec foo [] = foo [1]
  >         foo [_] = foo ["abc"]
  >         foo (_ :: xs) = foo xs
  > in foo []
  > EOF
  Error: Cannot unify unrelated types Int and String

But it should after adding explicit type annotations
  $ GenExpr << "EOF"
  > let rec foo : [a] -> ()
  >         foo [] = foo [1]
  >         foo [_] = foo ["abc"]
  >         foo (_ :: xs) = foo xs
  > in foo []
  > EOF
  let rec { (foo : (\a$1. [a$1] -> ())) = \($0 : [$20]) -> match ($0 : [$20]) with { (::) ($1 : $20) ($2 : [$20]) -> match ($2 : [$20]) with { (::) ($3 : $20) ($4 : [$20]) -> let (xs : [$20]) = ($2 : [$20]) in (foo : (\a$1. [a$1] -> ())) (@$20) (xs : [$20]); [] -> (foo : (\a$1. [a$1] -> ())) (@String) ((::) "abc" []); }; [] -> (foo : (\a$1. [a$1] -> ())) (@Int) ((::) 1 []); } } in (foo : (\a$1. [a$1] -> ())) (@$23) []
  : ()
