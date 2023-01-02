  $ GenAst << "EOF"
  > match ((Cons x) Nil) with
  >   Cons (-2) xs | Cons 3 xs -> "Ok"
  >   _ -> "Else"
  > 
  > def find : (a -> Bool) -> [a] -> Option a
  >     find p xs =
  >       let rec loop xs = match xs with
  >                 x :: xs -> if p x then Some x
  >                                   else loop xs
  >                 [] -> None in loop xs
  > 
  >     any : (a -> Bool) -> [a] -> Bool
  >     any p xs =
  >       match find p xs with Some _ -> True; _ -> false
  > 
  > any q ((::) 'a' ['b', 'c'])
  > 
  > \match
  >   [x, y, z] -> True
  >   [x] -> True
  >   _ -> False
  > EOF
  match ((Cons x) Nil) with { ((Cons (-2) xs)|(Cons 3 xs)) -> "Ok"; _ -> "Else"; }
  def { find : (((->) (((->) a) Bool)) (((->) ([] a)) (Option a))); find p xs = let rec { loop xs = match xs with { ((::) x xs) -> if (p x) then (Some x) else (loop xs); [] -> None; }; } in (loop xs); any : (((->) (((->) a) Bool)) (((->) ([] a)) Bool)); any p xs = match ((find p) xs) with { (Some _) -> True; _ -> false; }; }
  ((any q) ((::) '\u0061' ['\u0062', '\u0063']))
  (\match { [x, y, z] -> True; [x] -> True; _ -> False; })
