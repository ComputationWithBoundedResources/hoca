let cons x xs = Cons(x,xs) ;;		    

let comp f g x = f (g x) ;;
  
let rec walk t = 
  match t with 
  | Leaf(x) -> cons x
  | Node(t1,t2) -> comp (walk t1) (walk t2)
;;

walk t Nil

