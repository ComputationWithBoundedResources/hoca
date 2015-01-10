let id x = x ;;	     
let comp f g x = f (g x) ;;
let cons x xs = Cons(x,xs) ;;

(* rev :: list -> list *)
let rev l =
  (* walk :: list -> (list -> list) *)
  let rec walk l = 
    match l with 
    | Nil -> id
    | Cons(x,xs) -> comp (walk xs) (cons x)
  in walk l Nil
;;	  

  rev l
	  
