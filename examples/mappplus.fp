let rec map f xs = 
  match xs with
  | Nil -> Nil 
  | Cons(x,xs') -> Cons(f x, map f xs')
;;
  
let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;	      

  map (plus x) l


    
