type 'a list = Nil | Cons of 'a * 'a list
;;

type int = 0 | S of int | M of int
;;
    

(* max : nat -> nat -> nat *)
let rec max x y = 
  match x with
    | 0 -> y
    | S(x') -> 
       match y with
       | 0 -> x
       | S(y') -> S(max x' y')
;;

(* plus : nat -> nat -> nat *)  
let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;

(* minus : nat -> nat -> nat *)  
let rec minus x y = 
  match x with
  | 0 -> 0
  | S(x') ->
     match y with
     | 0 -> x
     | S(y') -> minus x' y'
;;
  
(* foldl: (nat -> nat -> nat) -> nat -> nat list -> nat *)
let rec foldl f z xs = 
  match xs with 
  | Nil -> z
  | Cons(x,xs') -> foldl f (f z x) xs'
;;

(* maxlist : int list -> int *)  
let maxlist = foldl max 0 ;;
  
(* scanr: (nat -> nat -> nat) -> nat -> nat list -> nat list *)
let rec scanr f z xs =
  match xs with
  | Nil -> Cons(z,Nil)
  | Cons(x,xs') -> 
     match scanr f z xs' with
     | Nil -> error
     | Cons(y,ys) -> Cons(f x y, Cons(y,ys))
;;

let mms l =
  (* f x y == max 0 (plus x y) *)
  let rec f x y =
    match x with
    | 0 ->
       (match y with
	| 0 -> 0
	| M(y') -> 0
	| S(y') -> y)
    | M(x') ->
       (match y with
	| 0 -> 0
	| M(y') -> 0
	| S(y') -> minus y x')
    | S(x') ->
       (match y with
	| 0 -> x
	| M(y') -> minus x y'
	| S(y') -> plus x y)       
  in maxlist (scanr f 0 l)
;;

