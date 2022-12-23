# RKM

Here we try to implement all of the language specified in the main branch but with these changes:
*  Whitespace occasionally matters, which will allow fewer `;` and `{...}`s.
This is inspired by all these whitespace-significant languages.
Of course, explicit braces are still allowed.
*  Much less restrictions on operators. Essentially operators follow a predefined precedence based on the characters (see below). In addition, data constructors can also be defined as operators. They must begin with `:` and the precedence / associativity is determined based on what's after the `:`. **Note that** prefix data constructor operators cannot be `!` nor `-`.
*  Add scoped type variables. They were basically not allowed (in expression contexts) in the original implementation.
*  Slightly better REPL by adding some commands to inspect the values / types.
*  Actually try to write tests :sweatsmile:

  Level | Operator | Associativity
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

## Sample Snippet

```
data MyList a = Cons a (MyList a)
              | Nil

def pack (x : a) (y : b) = (x, y)
def tail = \match
  Cons _ xs -> xs
  Nil -> Nil

def map : (a -> b) -> MyList a -> MyList b
    map f = \match
      Nil -> Nil
      Cons x xs -> Cons (f x) (map f xs)
```