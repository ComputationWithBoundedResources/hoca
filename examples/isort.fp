let rec leq x y = 
  match x with
    | 0 -> True
    | S(x') -> 
       match y with
       | 0 -> False
       | S(y') -> leq x' y'
;;
let rec insert ord x ys = 
  match ys with 
  | Nil -> Cons(x,Nil)
  | Cons(y,ys') -> 
     match ord x y with 
     | True -> Cons(x,Cons(y,ys'))
     | False -> Cons(y,insert ord x ys')
;;
let rec sort ord ys = 
  match ys with 
  | Nil -> Nil
  | Cons(y,ys') -> 
     insert ord y (sort ord ys')
;;

  sort leq ys

		
	   
