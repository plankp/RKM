  $ GenKind << "EOF"
  > type Id x = x
  >      App f v = f v
  > type IntToChar = Id (App App App (->) Int Char)
  >      Partial = Id (App App App (->) String)
  > EOF
  (->) = (->) : * -> * -> *
  App = (\f$3. (\v$5. f$3 v$5)) : (\$10. (\$11. ($10 -> $11) -> $10 -> $11))
  Bool = Bool : *
  Char = Char : *
  Id = (\x. x) : (\$9. $9 -> $9)
  Int = Int : *
  IntToChar = Int -> Char : *
  Partial = (->) String : * -> *
  String = String : *
  [] = [] : * -> *
  ref = ref : * -> *
