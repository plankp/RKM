  $ ../GenKind.exe << "EOF"
  > type Id x = x
  >      App f v = f v
  > type IntToChar = Id (App App App (->) Int Char)
  >      Partial = Id (App App App (->) String)
  > EOF
  (->) = (->) : * -> * -> *
  App = (\f. (\v. f v)) : (\$2. (\$3. ($2 -> $3) -> $2 -> $3))
  Char = Char : *
  Id = (\x. x) : (\$0. $0 -> $0)
  Int = Int : *
  IntToChar = Int -> Char : *
  Partial = (->) String : * -> *
  String = String : *
