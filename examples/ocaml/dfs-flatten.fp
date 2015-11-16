
(* flatten example from 'Static Determination of Quantitative Resource Usage for Higher-Order Programs' by Jost et. al. *)

type 'a tree = Leaf of 'a | Node of 'a tree * 'a tree
;;
type 'a list = Nil | Cons of 'a * 'a list
;;

let cons x xs = Cons(x,xs) ;;
  
let rec dfsAcc g t acc =
  match t with
  | Leaf(x) -> g x acc
  | Node(t1,t2) -> dfsAcc g t2 (dfsAcc g t1 acc)
;;
  
							
let rec revApp l acc =
  match l with
  | Nil -> acc
  | Cons(y,ys) -> revApp ys Cons(y,acc)
;;

let flatten t = revApp (dfsAcc cons t Nil) Nil
;;
