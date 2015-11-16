(* Richard Bird: Introduction to functional programming using Haskell, Section 7.2 *)

type 'a list = Nil | Cons of 'a * 'a list
;;

let rec foldl f z xs = 
  match xs with 
  | Nil -> z
  | Cons(x,xs') -> foldl f (f z x) xs'
;;

let prefix xs x = Cons(x,xs);;
  
let rev l = foldl prefix Nil l;;
    
