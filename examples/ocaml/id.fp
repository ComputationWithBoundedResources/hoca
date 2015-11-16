type nat = 0 | S of nat
;;

let rec iter f g x = 
  match x with  
  | 0 -> g
  | S(x') -> f (iter f g x')
;;
let compS f z = f (S(z))
;;		  
let id y = y
;;	     

let iterid n = iter compS id n 0
;;  
