(* from Sereni: Size-Change Termination of Higher-Order Functional Programs; PRG-RR-04-20 *)

type 'a tree = Leaf of 'a | Node of 'a tree * 'a tree
;;

type nat = 0 | S of nat
;;

type ('a,'b) pair = P of 'a * 'b
;;    

let fix f =
  let rec x = lazy (force (f x))
  in x
;;

let rec min a b =
  match a with
  | 0 -> 0
  | S(a') ->
     match b with
     | 0 -> 0
     | S(b') -> S(min a' b')
;;

let fst p = match p with | P(a,b) -> a
and snd p = match p with | P(a,b) -> b
;;				       
  
let rec rpm t m =
  match t with
  | Leaf(x) -> lazy P((lazy Leaf(force m)), (lazy x))
  | Node(t1,t2) ->
     let p1 = force (rpm t1 m)
     and p2 = force (rpm t2 m)
     in lazy P((lazy Node(force (fst p1), force (fst p2))), 
	       (lazy (min (force (snd p1)) (force (snd p2)))))
;;

let repmin t =
  let f p = rpm t (lazy (force (snd (force p)))) in
  force (fst (force (fix f)))
;;
