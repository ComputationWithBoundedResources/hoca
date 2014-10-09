let rec fold f z xs = 
  match xs with
  | Nil -> z
  | Cons(x,xs') -> f x (fold f z xs')
in 
let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
in fun l -> fold plus 0 l


    
