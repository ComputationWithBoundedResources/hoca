let comp f g x = f (g x) ;;
  
(* rev :: list -> list *)
let rev l =
  (* walk :: list -> (list -> list) *)
  let rec walk xs = 
    match xs with 
    | Nil -> (fun x -> x)
    | Cons(x,xs') ->
       comp (walk xs') (fun ys -> Cons(x,ys))
  in walk l Nil
;;	  
	  
