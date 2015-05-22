let rec foldr f z xs = 
  match xs with 
  | NilF -> z
  | ConsF(x,xs') -> f x (foldr f z xs')
;;
  
let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;; 

let rec mapF f xs = 
  match xs with
  | Nil -> NilF 
  | Cons(x,xs') -> ConsF(f x, mapF f xs')
;; 

let comp f g z = f (g z)
;;

let id x = x
;;

let foldsum l = foldr comp id (mapF plus l) 0
;;
