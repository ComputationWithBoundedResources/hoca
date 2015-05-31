type Unit = Unit
;;

type nat = 0 | S of nat
;;

type 'a list = Nil | Cons of 'a * 'a list
;;

type ('a,'b) pair = Pair of 'a * 'b
;;

type 'a option = None | Some of 'a
;;    

let rec plus x y = 
  match x with
  | 0 -> y
  | S(x') -> S(plus x' y)
;;	      

let rec equal x y =
  match x with
  | 0 ->
     (match y with
      | 0 -> True
      | S(y') -> False)
  | S(x') ->
     (match y with
      | 0 -> False
      | S(y') -> equal x' y')
;;       
  
let rec find key l =
   match l with
   | Nil -> None
   | Cons(p,l') ->
      match p with
      | Pair(k,v) ->
	 match equal k key with
	 | True -> Some(v)
	 | False -> find key l'
;;			 
  
(* state monad *)
let return a = fun s -> Pair(s,a)
;;
  
let bind m f = fun s ->
  match m s with
  | Pair(s',a) -> f a s'
;;

let bind' m1 m2 = bind m1 (fun r -> m2)
;;		       
  
let get = fun s -> Pair(s,s)
;;

let put s = fun s' -> Pair(s',Unit)
;;

let modify f = fun s -> Pair(f s, Unit)
;;
  
(* evalState :: State s a -> s -> a *)
let evalState m s =
  match m s with
  | Pair(s,a) -> a
;; 		     

let liftM f m = bind m (fun r -> return (f r))
;;		     

let liftM2 f m1 m2 = bind m1 (fun r1 -> bind m2 (fun r2 -> return (f r1 r2)))
;;		     
  
let memoM m v =
  let lookupM = liftM (find v) get
  and insertM a = modify (fun c -> Cons(Pair(v,a),c))
  in bind lookupM
	  (fun r ->
	   match r with
	   | None -> bind (m v)
			  (fun a -> bind' (insertM a) (return a))
	   | Some(a) -> return a)
;;	   
       
let rec fibM n =
  match n with
  | 0 -> return S(0)
  | S(n') ->
     match n' with
     | 0 -> return S(0)
     | S(n'') ->
	liftM2 plus (memoM fibM n') (memoM fibM n'')
;;		     

let fib n = evalState (fibM n) Nil
;;
