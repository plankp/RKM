  $ ../GenAst.exe << "EOF"
  > // list decons
  > match e with _ :: _ | _ :: _ :: _ -> a; _ -> b;
  > match e with _ :: (_ | _) :: _ :: _ -> a; _ -> b;
  > EOF
  match e with { (((::) _ _)|((::) _ ((::) _ _))) -> a; _ -> b; }
  match e with { ((::) _ ((::) (_|_) ((::) _ _))) -> a; _ -> b; }
