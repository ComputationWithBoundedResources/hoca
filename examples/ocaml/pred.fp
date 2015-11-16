
type nat = 0 | S of nat
;;

let pred x =
  match x with
  | 0 -> 0
  | S(x') -> x'
;;
