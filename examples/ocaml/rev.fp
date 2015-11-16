type 'a list = Nil | Cons of 'a * 'a list
;;

let rec append xs ys = 
  match xs with 
  | Nil -> ys
  | Cons(x,xs') -> Cons(x, append xs' ys) 
;;
  
let rec rev xs =
  match xs with 
  | Nil -> Nil
  | Cons(x,xs') -> append (rev xs') Cons(x,Nil)
;;			  
