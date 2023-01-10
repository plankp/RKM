# RKM

Yet another programming language.

Motivation is that at some point of implementing QKM,
we realized that type classes in Haskell are really cool,
and so here we try to implement them.
(and we do end up implementing single parameter type classes)

## Requirements and Build Instructions

Check the `dune-project` file for required dependencies.
The project can be built using `opam` or `dune`.

It builds an executable called `rkmi`,
which launches the interpreter

## Sample Snippet

```
type MyList a =
       | Cons a (MyList a)
       | Nil

def pack (x : a) (y : b) = (x, y)
def tail = \match
  Cons _ xs -> xs
  Nil -> Nil

def map : (a -> b) -> MyList a -> MyList b
    map f (Cons x xs) = Cons (f x) (map f xs)
    map _ Nil = Nil
```

Note that due to how the interpreter work,
the easiest way to try this snippet would be to save it on disk somewhere,
and use `:load file` (replace `file` with the actual location + name of the file) in the interpreter to load it.

## Extra Notes

This is my humble attempt at documenting
aspects of the language that have dramatically changed from an earlier version of this language.

### REPL Commands

*  `:q`, `:quit` to quit
*  `:k`, `:kind` to evaluate a type annotation
*  `:t`, `:type` to get the type (and the internal representation) of an expression
*  `:tctors` to list all the type constructors (does not include traits)
*  `:reset` to reset the runtime environment
*  `:load` to load a external script

These must appear at the beginning of a logical block.
Usually this refers to a single line,
but it may be multiple lines if a line ends with a backslash (`\\`).

### Alignment / Whitespace Sensitivity

Inspired by Haskell,
unless explicitly delimited using balanced `{ ... }` and `;`'s,
certain constructs cause the expected alignment to change.

In informal terms,
declaration-ish or pattern matching constructs are affected by this.
These include — with the affected regions indicated with `{ ... }`:

*  `let rec { ... }` and `let { ... }`
*  `\\case { ... }` and `match ... with { ... }`
*  `def { ... }`
*  `extern { ... }`
*  `type { ... }`
*  `trait ... with { ... }`
*  `impl ... with { ... }`

### Scoped Type Variables

While this seems like such an obvious feature to have,
the original implementation basically did not allow them at all.

We sort of have them in this new revision.
Only pattern matches can introduce them.

Explicit type annotations of the let (and let rec) bindings *do not* introduce new type variables.
The rule is that the type variables that are not in scope become `forall`-ed:

```
// The type of y is forall b. b -> a where a is refering to the one at (x : a).
// Since b is not scoped, the body of y cannot refer to b.
\(x : a) -> let y : b -> a; y _ = x in y ()
```

A similar phenomenon (where the body cannot refer to these type variables) occurs with trait implementations.

### Custom Operators

Generally speaking,
any continuous sequence (so no comments nor whitespaces in between) of any of the following characters
form an operator:

```
+  -  *  /  <  =  >  :
|  ^  &  %  !  ~  @
```

Some operators have fixed special meaning:

*  `=>` for specifying trait requirements
*  `->` for functions and pattern matching
*  `&&` and `||` for boolean short circuiting
*  `=` for mutating `ref` cells
*  `:` for explicit type annotations
*  `|` for defining and matching alternate patterns (but can be redefined in most other contexts)

Aside from `:`,
all other operators that start with `:` are reserved as data constructor names.

The precedence for both expression and pattern matching contexts roughly follow this table,
with the data constructor operators being `:` followed by the operators with trailing `...`:

  Level | Operator  | Associativity
--------|-----------|---------------
1       | `=` | right
2       | `\|\|` | left
3       | `&&` | left
4       | `!`..., `=`..., `<`..., `>`... | left
5       | `@`... | right
6       | `:`... | right
7       | `+`..., `-`..., `\|`..., `^`... | left
8       | `*`..., `/`..., `%`..., `&`... | left
9       | `!`, `-`, `~`... | right (prefix)

All customizable operators (the ones with trailing `...` in the table) can be referenced using `(...)`
(e.g., the `+` becomes `(+)` and so on).
Note that prefix operators `!` and `-` are aliases of the names `not` and `negate`.
