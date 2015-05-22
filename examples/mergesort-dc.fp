let rec mapL f xs = 
  match xs with
  | NilL -> NilL 
  | ConsL(x,xs') -> ConsL(f x, mapL f xs')
;;

let rec length xs =
  match xs with
  | Nil -> 0
  | Cons(x,xs') -> S(length xs')
;;

let rec leq x y = 
  match x with
    | 0 -> True
    | S(x') -> 
       match y with
       | 0 -> False
       | S(y') -> leq x' y'
;;

let const f x = f;;  

let rec halve x =
  match x with
  | 0 -> 0
  | S(x') ->
     match x' with
     | 0 -> S(0)
     | S(x'') -> S(halve x'')
;;

let tail l =
  match l with
  | Nil -> Tail_error_empty_list
  | Cons(l,ls) -> ls
;;		    

let head l =
  match l with
  | Nil -> Head_error_empty_list
  | Cons(l,ls) -> l
;;
  
let rec take n l =
  match n with
  | 0 -> Nil
  | S(n') -> Cons(head l, take n' (tail l))
;; 

let rec drop n l =
  match n with
  | 0 -> l
  | S(n') -> drop n' (tail l)
;; 


let divideAndConquer isDivisible solve divide combine initial =
  let rec dc pb = 
    match isDivisible pb with
    | False -> solve pb
    | True -> combine pb (mapL dc (divide pb))
  in dc initial
;;

let rec merge ys zs = 
  match ys with
  | Nil -> zs
  | Cons(y,ys') ->
     match zs with
     | Nil -> ys
     | Cons(z,zs') ->
	match leq y z with
	| True -> Cons(y,merge ys' zs)
	| False -> Cons(z,merge ys zs')
;;
  
let mergesort zs = 
  let divisible ys =
    match ys with
    | Nil -> False
    | Cons(y,ys') ->
       match ys' with
       | Nil -> False
       | Cons(y',ys'') -> True
  and divide ys =
    let n = halve (length ys)
    in ConsL(take n ys, ConsL(drop n ys,NilL))
  and combine p =
    match p with
    | ConsL(l1,p') ->
       match p' with
       | ConsL(l2,p'') -> merge l1 l2
  in divideAndConquer divisible (fun ys -> ys) divide (const combine) zs
;;

