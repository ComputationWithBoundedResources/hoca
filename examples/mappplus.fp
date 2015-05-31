type nat = 0 | S of nat
;;

type 'a list = Nil | Cons of 'a * 'a list
;;

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

let mapplus l x = map (plus x) l
;;  


    
