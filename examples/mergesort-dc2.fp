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

let rec split ys xs1 xs2 =
  match ys with
  | Nil -> ConsL(xs1, ConsL(xs2,NilL))
  | Cons(y,ys') -> split ys' Cons(y,xs2) xs1
;;			 
		
let mergesort = 
  let divisible ys =
    match ys with
    | Nil -> False
    | Cons(y,ys') ->
       match ys' with
       | Nil -> False
       | Cons(y',ys'') -> True
  and divide ys = split ys Nil Nil
  and combine p =
    match p with
    | ConsL(l1,p') ->
       match p' with
       | ConsL(l2,p'') -> merge l1 l2
  in divideAndConquer divisible (fun ys -> ys) divide (const combine)
;;

mergesort zs
