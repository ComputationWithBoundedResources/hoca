type nat = 0 | S of nat;;
type bool = True | False ;;

let rec even x =
  match x with
  | 0 -> True
  | S(x') -> odd x'
and odd x = 
  match x with
  | 0 -> False
  | S(x') -> even x'
;;

let main x = even x ;;
  
