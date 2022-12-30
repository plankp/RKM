In this case, all a's refer to the same type, so we don't generalize, meaning
this example fails because a ~ Char and a ~ String is impossible
  $ GenExpr << "EOF"
  > {\(x : a) -> let id : a -> a; id x = x in (id 'v', id "v")}
  > EOF
  Error: Cannot unify unrelated types Char and String

In this case, a is not in the enclosing scope, and therefore, we generalize
  $ GenExpr << "EOF"
  > {\x -> let id : a -> a; id x = x in (id 'v', id "v")}
  > EOF
  \($0 : $3) -> let (x : $3) = ($0 : $3) in let (id$1 : (\a$8. a$8 -> a$8)) = \ @a$8 -> \($0 : a$8) -> let (x : a$8) = ($0 : a$8) in (x : a$8) in let (id : (\a$8. a$8 -> a$8)) = (id$1 : (\a$8. a$8 -> a$8)) in ((id : (\a$8. a$8 -> a$8)) (@Char) '\u0076', (id : (\a$8. a$8 -> a$8)) (@String) "v")
  : $3 -> (Char, String)

As a consequence, bindings do not introduce new type variables, meaning the
following fails
  $ GenExpr << "EOF"
  > {\x -> let id : a -> a; id x = x : a in ()}
  > EOF
  Error: unknown type variable named a

And a nasty nasty related quantized type variables escaping their scope
  $ GenExpr << "EOF"
  > {\x -> let bad : [a] -> [a]; bad xs = x :: xs in bad []}
  > EOF
  Error: Unification of types $3 with a$10 would result in loss of generality
  Error: Unification of types $3 with a$10 would result in loss of generality

Without the annotation, it does the right thing (and not generalize)
  $ GenExpr << "EOF"
  > {\x -> let bad xs = x :: xs in bad []}
  > EOF
  \($0 : $3) -> let (x : $3) = ($0 : $3) in let (bad$1 : [$3] -> [$3]) = \($0 : [$3]) -> let (xs : [$3]) = ($0 : [$3]) in ((::) (x : $3) (xs : [$3]) : [$3]) in let (bad : [$3] -> [$3]) = (bad$1 : [$3] -> [$3]) in (bad : [$3] -> [$3]) ([] : [$3])
  : $3 -> [$3]

(or generalize)
  $ GenExpr << "EOF"
  > {let id x = x in (id 'a', id "z")}
  > EOF
  let (id$1 : (\$5. $5 -> $5)) = \ @$5 -> \($0 : $5) -> let (x : $5) = ($0 : $5) in (x : $5) in let (id : (\$5. $5 -> $5)) = (id$1 : (\$5. $5 -> $5)) in ((id : (\$5. $5 -> $5)) (@Char) '\u0061', (id : (\$5. $5 -> $5)) (@String) "z")
  : (Char, String)

As hinted by a previous test case, we make sure the initializers are general
enough
  $ GenExpr << "EOF"
  > {let p2 : a -> b -> (a, b); p2 x y = (x, y) in p2}
  > EOF
  let (p2$1 : (\a$9. (\b$10. a$9 -> b$10 -> (a$9, b$10)))) = \ @a$9 -> \ @b$10 -> \($0 : a$9) -> \($1 : b$10) -> let (y : b$10) = ($1 : b$10) in let (x : a$9) = ($0 : a$9) in ((x : a$9), (y : b$10)) in let (p2 : (\a$9. (\b$10. a$9 -> b$10 -> (a$9, b$10)))) = (p2$1 : (\a$9. (\b$10. a$9 -> b$10 -> (a$9, b$10)))) in (p2 : (\a$9. (\b$10. a$9 -> b$10 -> (a$9, b$10)))) (@a$18) (@b$19)
  : a$18 -> b$19 -> (a$18, b$19)

  $ GenExpr << "EOF"
  > {let p2 : a -> a -> c; p2 x y = (x, y) in p2}
  > EOF
  Error: Cannot unify unrelated types c$10 and (a$9, a$9)

And the identifier takes the type you provide (even if the inferred type is
more general)
  $ GenExpr << "EOF"
  > {let p2 : a -> a -> (a, a); p2 x y = (x, y) in p2}
  > EOF
  let (p2$1 : (\a$7. a$7 -> a$7 -> (a$7, a$7))) = \ @a$7 -> \($0 : a$7) -> \($1 : a$7) -> let (y : a$7) = ($1 : a$7) in let (x : a$7) = ($0 : a$7) in ((x : a$7), (y : a$7)) in let (p2 : (\a$7. a$7 -> a$7 -> (a$7, a$7))) = (p2$1 : (\a$7. a$7 -> a$7 -> (a$7, a$7))) in (p2 : (\a$7. a$7 -> a$7 -> (a$7, a$7))) (@a$15)
  : a$15 -> a$15 -> (a$15, a$15)

Underscores do work, essentially they always generalize (but they're not that
useful because you can refer to them)
  $ GenExpr << "EOF"
  > {let ignore : _ -> (); ignore _ = () in (ignore 'v', ignore "v")}
  > EOF
  let (ignore$1 : (\_$5. _$5 -> ())) = \ @_$5 -> \($0 : _$5) -> () in let (ignore : (\_$5. _$5 -> ())) = (ignore$1 : (\_$5. _$5 -> ())) in ((ignore : (\_$5. _$5 -> ())) (@Char) '\u0076', (ignore : (\_$5. _$5 -> ())) (@String) "v")
  : ((), ())

Another slight annoyance is "value restriction" which means not all things are
allowed generalize. One such example is function calls.
  $ GenExpr << "EOF"
  > {
  > let not_id = (\x -> x) (\x -> x)
  > in (not_id 'v', not_id "v")
  > }
  > EOF
  Error: Cannot unify unrelated types Char and String

We also want to make sure we can't trick it into becoming generalized!
  $ GenExpr << "EOF"
  > {
  > let not_id : a -> a
  >     not_id = (\x -> x) (\x -> x)
  > in (not_id 'v', not_id "v")
  > }
  > EOF
  Error: Unification of types $15 with a$5 would result in loss of generality
  Error: Unification of types $15 with a$5 would result in loss of generality

The common cited workaround is to use eta-expansion
  $ GenExpr << "EOF"
  > {
  > let id : a -> a
  >     id x = (\x -> x) (\x -> x) x
  > in (id 'v', id "v")
  > }
  > EOF
  let (id$1 : (\a$5. a$5 -> a$5)) = \ @a$5 -> \($0 : a$5) -> let (x : a$5) = ($0 : a$5) in (\($0 : a$5 -> a$5) -> let (x : a$5 -> a$5) = ($0 : a$5 -> a$5) in (x : a$5 -> a$5)) (\($0 : a$5) -> let (x : a$5) = ($0 : a$5) in (x : a$5)) (x : a$5) in let (id : (\a$5. a$5 -> a$5)) = (id$1 : (\a$5. a$5 -> a$5)) in ((id : (\a$5. a$5 -> a$5)) (@Char) '\u0076', (id : (\a$5. a$5 -> a$5)) (@String) "v")
  : (Char, String)

Test case for relaxed value restriction
  $ GenExpr << "EOF"
  > {
  > let snd : (a, b) -> b
  >     snd (_, y) = y in
  > let tst : [a]
  >     tst = snd ("", []) in
  > tst
  > }
  > EOF
  let (snd$1 : (\a$7. (\b$8. (a$7, b$8) -> b$8))) = \ @a$7 -> \ @b$8 -> \($0 : (a$7, b$8)) -> match ($0 : (a$7, b$8)) with { (($1 : a$7), ($2 : b$8)) -> let (y : b$8) = ($2 : b$8) in (y : b$8); } in let (snd : (\a$7. (\b$8. (a$7, b$8) -> b$8))) = (snd$1 : (\a$7. (\b$8. (a$7, b$8) -> b$8))) in let (tst$1 : (\a$18. [a$18])) = \ @a$18 -> (snd : (\a$7. (\b$8. (a$7, b$8) -> b$8))) (@String) (@[a$18]) ("", ([] : [a$18])) in let (tst : (\a$18. [a$18])) = (tst$1 : (\a$18. [a$18])) in (tst : (\a$18. [a$18])) (@a$28)
  : [a$28]

Also must examine the polymorphic recursion case. This should not type check.
  $ GenExpr << "EOF"
  > {
  > let rec foo [] = foo [1]
  >         foo [_] = foo ["abc"]
  >         foo (_ :: xs) = foo xs
  > in foo []
  > }
  > EOF
  Error: Cannot unify unrelated types Int and String

But it should after adding explicit type annotations
  $ GenExpr << "EOF"
  > {
  > let rec foo : [a] -> ()
  >         foo [] = foo [1]
  >         foo [_] = foo ["abc"]
  >         foo (_ :: xs) = foo xs
  > in foo []
  > }
  > EOF
  let rec { (foo : (\a$6. [a$6] -> ())) = \ @a$6 -> \($0 : [a$6]) -> match ($0 : [a$6]) with { [] -> (foo : (\a$6. [a$6] -> ())) (@Int) ((::) 1 ([] : [Int]) : [Int]); (::) ($1 : a$6) ($2 : [a$6]) -> match ($2 : [a$6]) with { [] -> (foo : (\a$6. [a$6] -> ())) (@String) ((::) "abc" ([] : [String]) : [String]); _ -> let (xs : [a$6]) = ($2 : [a$6]) in (foo : (\a$6. [a$6] -> ())) (@a$6) (xs : [a$6]); }; } } in (foo : (\a$6. [a$6] -> ())) (@a$24) ([] : [a$24])
  : ()
