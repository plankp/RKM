  $ GenKind << "EOF"
  > type Id x = x
  >      App f v = f v
  > type IntToChar = Id (App App App (->) Int Char)
  >      Partial = Id (App App App (->) String)
  > EOF
  (->) = (->) : * -> * -> *
  App = (\f$3. (\v$5. f$3 v$5)) : (\$8. (\$9. ($8 -> $9) -> $8 -> $9))
  Bool = Bool : *
  Char = Char : *
  Id = (\x. x) : (\$2. $2 -> $2)
  Int = Int : *
  IntToChar = Int -> Char : *
  Partial = (->) String : * -> *
  String = String : *
  [] = [] : * -> *
  ref = ref : * -> *
