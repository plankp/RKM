  $ ../GenAst.exe << "EOF"
  > // make sure the general shift-reduce logic is correct
  > x + y * z + w;
  > x * y + z + w;
  > x + y + z * w;
  > 
  > // some ops have the same prefix but have special prec levels
  > a << b <+ c;
  > a <+ b << c;
  > a >> b >+ c;
  > a >+ b >> c;
  > a && b &+ c;
  > a &+ b && c;
  > a || b |+ c;
  > a |+ b || c;
  > 
  > // right associative operators
  > x :: y :: z;
  > a @@ b @@ c;
  > a = b = c;
  > 
  > // also prefix operators are weird
  > !a != -b -< ~c;
  > -sin x;     // - (sin x)
  > -sin -x;    // (-sin) - x
  > -sin (-x);  // -(sin(-x))
  > 
  > // test the prec levels for bitwise operators (<<, >>, &)
  > a << b * c;
  > a * b << c;
  > a >> b * c;
  > a * b >> c;
  > a & b * c;
  > a * b & c;
  > 
  > // same thing for (|, ^)
  > a | b + c;
  > a + b | c;
  > a ^ b + c;
  > a + b ^ c;
  > EOF
  ((x + (y * z)) + w)
  (((x * y) + z) + w)
  ((x + y) + (z * w))
  ((a << b) <+ c)
  (a <+ (b << c))
  ((a >> b) >+ c)
  (a >+ (b >> c))
  (a && (b &+ c))
  ((a &+ b) && c)
  (a || (b |+ c))
  ((a |+ b) || c)
  ((::) x ((::) y z))
  (a @@ (b @@ c))
  (a = (b = c))
  ((!a) != ((-b) -< (~c)))
  (-(sin x))
  ((-sin) - x)
  (-(sin (-x)))
  ((a << b) * c)
  ((a * b) << c)
  ((a >> b) * c)
  ((a * b) >> c)
  ((a & b) * c)
  ((a * b) & c)
  ((a | b) + c)
  ((a + b) | c)
  ((a ^ b) + c)
  ((a + b) ^ c)
