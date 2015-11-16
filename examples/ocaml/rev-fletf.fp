type 'a list = Nil | Cons of 'a * 'a list
;;

let rec foldr f z xs = 
  match xs with 
  | Nil -> z
  | Cons(x,xs') -> f x (foldr f z xs')
;;

let fleft op e xs = 
  let step x f a = f (op a x)
  in foldr step (fun u -> u) xs e
;;

let rev l = fleft (fun xs x -> Cons(x,xs)) Nil l
;;
