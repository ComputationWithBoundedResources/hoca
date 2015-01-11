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
    | True ->
       match divide pb with
       | P(p1,p2) -> combine pb (dc p1) (dc p2)
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
  | Nil -> P(xs1, xs2)
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
  and combine = const merge
  and solve ys = ys
  in divideAndConquer divisible solve divide combine
;;

mergesort zs
