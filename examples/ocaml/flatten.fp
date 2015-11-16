type 'a list = Nil | Cons of 'a * 'a list;;
type 'a tree = Leaf of 'a | Node of 'a tree * 'a tree;;

let cons x xs = Cons(x,xs) ;;		    

let comp f g x = f (g x) ;;
  
let rec walk t = 
  match t with 
  | Leaf(x) -> cons x
  | Node(t1,t2) -> comp (walk t1) (walk t2)
;;

let flatten t = walk t Nil
;;  

