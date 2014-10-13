let rec leq x y = 
  match x with
    | 0 -> True
    | S(x') -> 
       match y with
       | 0 -> False
       | S(y') -> leq x' y'
in 
let rec insert ord x ys = 
  match ys with 
  | Nil -> Cons(x,Nil)
  | Cons(y,ys') -> 
     match ord x y with 
     | True -> Cons(x,Cons(y,ys'))
     | False -> Cons(y,insert ord x ys')
in 
let rec fold f z xs = 
  match xs with
  | Nil -> z
  | Cons(x,xs') -> f x (fold f z xs')
in 
fun ys -> fold (insert leq) Nil ys

		
	   
