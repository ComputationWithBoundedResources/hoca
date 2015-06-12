type 'a list = Nil | Cons of 'a * 'a list
;;

type Unit = Unit
;;

type 'a lazy_list = NilL | ConsL of 'a * (Unit -> 'a lazy_list)
;;

type nat = 0 | S of nat
;;

let rec take_l n xs =
  match force xs with
  | NilL -> Nil
  | ConsL(x,xs') ->
     match n with
     | 0 -> Nil
     | S(n') -> Cons(x,take_l n' xs')
;;		    

let rec zeros = lazy ConsL(0, zeros)
;;		     

let take_lazy n = take_l n zeros
;;  
