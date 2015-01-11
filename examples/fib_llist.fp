let rec zipwith_l f xs ys =
  lazy (match force xs with
	| NilL -> NilL
	| ConsL(x,xs') ->
	   match force ys with
	   | NilL -> NilL
	   | ConsL(y,ys') -> ConsL(f x y, zipwith_l f xs' ys'))
;; 

let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;	      

let tail_l xs =
  match force xs with
  | NilL -> Error_empty_list
  | ConsL(x,xs') -> xs'
;;		     
    
let rec nth_l n xs =
  match force xs with
  | NilL -> Error_nth_l
  | ConsL(x,xs') -> 
     match n with
     | 0 -> x
     | S(n') -> nth_l n' xs'
;;

let fix f =
  let rec x = lazy (force (f x))
  in x
;;

let rec take_l n xs =
  match force xs with
  | NilL -> Nil
  | ConsL(x,xs') ->
     match n with
     | 0 -> Nil
     | S(n') -> Cons(x,take_l n' xs')
;;		    
     
let rec fibs = lazy ConsL(0, lazy ConsL(S(0), zipwith_l plus fibs (tail_l fibs)))
;; 

take_l n fibs  
