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

  take_l n zeros		     
