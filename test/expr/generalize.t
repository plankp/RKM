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
  \$0 -> let x = $0 in let id$1 = \$0 -> let x = $0 in x in let id = id$1 in (id '\u0076', id "v")
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
  \$0 -> let x = $0 in let bad$1 = \$0 -> let xs = $0 in ((::) x xs : [$3]) in let bad = bad$1 in bad ([] : [$3])
  : $3 -> [$3]

(or generalize)
  $ GenExpr << "EOF"
  > {let id x = x in (id 'a', id "z")}
  > EOF
  let id$1 = \$0 -> let x = $0 in x in let id = id$1 in (id '\u0061', id "z")
  : (Char, String)

As hinted by a previous test case, we make sure the initializers are general
enough
  $ GenExpr << "EOF"
  > {let p2 : a -> b -> (a, b); p2 x y = (x, y) in p2}
  > EOF
  let p2$1 = \$0 -> \$1 -> let y = $1 in let x = $0 in (x, y) in let p2 = p2$1 in p2
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
  let p2$1 = \$0 -> \$1 -> let y = $1 in let x = $0 in (x, y) in let p2 = p2$1 in p2
  : a$15 -> a$15 -> (a$15, a$15)

Underscores do work, essentially they always generalize (but they're not that
useful because you can refer to them)
  $ GenExpr << "EOF"
  > {let ignore : _ -> (); ignore _ = () in (ignore 'v', ignore "v")}
  > EOF
  let ignore$1 = \$0 -> () in let ignore = ignore$1 in (ignore '\u0076', ignore "v")
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
  let id$1 = \$0 -> let x = $0 in (\$0 -> let x = $0 in x) (\$0 -> let x = $0 in x) x in let id = id$1 in (id '\u0076', id "v")
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
  let snd$1 = \$0 -> match $0 with { ($1, $2) -> let y = $2 in y; } in let snd = snd$1 in let tst$1 = snd ("", ([] : [a$18])) in let tst = tst$1 in tst
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
  let rec { foo = \$0 -> match $0 with { [] -> foo ((::) 1 ([] : [Int]) : [Int]); (::) $1 $2 -> match $2 with { [] -> foo ((::) "abc" ([] : [String]) : [String]); _ -> let xs = $2 in foo xs; }; } } in foo ([] : [a$24])
  : ()

Some nasty cases related to using ref-based weak types
  $ GenKind << "EOF"
  > type A a = a; B = A
  > EOF
  (->) = (->) : * -> * -> *
  A = (\a. a) : (\$4. $4 -> $4)
  B = (\a. a) : (\$5. $5 -> $5)
  Bool = Bool : *
  Char = Char : *
  Int = Int : *
  String = String : *
  [] = [] : * -> *
  ref = ref : * -> *

  $ GenExpr << "EOF"
  > { let rec id x = x; q () = id in () }
  > EOF
  let rec { id = \$0 -> let x = $0 in x ; q = \$0 -> match $0 with { () -> id; } } in ()
  : ()
