let rec map f xs = 
  case xs of
    Nil -> Nil; 
    Cons(x,xs') -> Cons(f x, map f xs');
in 
let rec plus x y = 
  case x of 
    0 -> y; 
    S(x') -> S(plus x' y);
in \ l x . map (plus x) l


    
