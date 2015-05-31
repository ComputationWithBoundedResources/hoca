type nat = 0 | S of nat
;;

type 'a list = Nil | Cons of 'a * 'a list
;;

let rec foldr f z xs = 
  match xs with 
  | Nil -> z
  | Cons(x,xs') -> f x (foldr f z xs')
;;
  
let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;; 

let rec map f xs = 
  match xs with
  | Nil -> Nil
  | Cons(x,xs') -> Cons(f x, map f xs')
;; 

let comp f g z = f (g z)
;;

let id x = x
;;

let foldsum l = foldr comp id (map plus l) 0
;;
