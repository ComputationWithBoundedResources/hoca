type 'a list = Nil | Cons of 'a * 'a list
;;

type nat = 0 | S of nat
;;

type 'a option = None | Some of 'a
;;

let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;	      

let rec mult x y =
  match x with
  | 0 -> 0
  | S(x') -> plus y (mult x' y)
;;

let square x = mult x x
;;

let rec unfoldr f z =
  match f z with
  | None -> Nil
  | Some(z') -> Cons(z',unfoldr f z')
;;

let countdown m =
  match m with
  | 0 -> None
  | S(m') -> Some(m')
;;

let enum n =
  match n with
  | 0 -> Nil
  | S(n') -> Cons(n, unfoldr countdown n)
;;		 
    
let rec map f xs = 
  match xs with
  | Nil -> Nil 
  | Cons(x,xs') -> Cons(f x, map f xs')
;;

let rec sum xs =
  match xs with
  | Nil -> 0
  | Cons(x,xs') -> plus x (sum xs')
;;			
  
let sum_sqs n = sum (map square (enum n))
;;
