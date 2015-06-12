
type 'a list = Nil | Cons of 'a * 'a list
;;

type nat = 0 | S of nat
;;

let rec fold f z xs = 
  match xs with
  | Nil -> z
  | Cons(x,xs') -> f x (fold f z xs')
;;

let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;

let sum l = fold plus 0 l
;;  


    
