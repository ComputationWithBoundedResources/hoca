type char = A | B | C;;

type nat = 0 | S of nat
;;

type 'a list = Nil | Cons of 'a * 'a list
;;

type 'a option = None | Some of 'a
;;    

type Unit = Unit
;;

let rec max x y =
  match x with
  | 0 -> y
  | S(x') ->
     match y with
     | 0 -> x
     | S(y') -> S(max x' y')
;;

let not b =
  match b with
  | True -> False
  | False -> True
;;
  
let eqChar x y =
  match x with
  | A -> (match y with
	  | A -> True
	  | B -> False
	  | C -> False)
  | B -> (match y with
	  | A -> False
	  | B -> True
	  | C -> False)
  | C -> (match y with
	  | A -> False
	  | B -> False
	  | C -> True)
;;	   
	
  
(* 
  type 'a parser = 'a SuccCont -> FailCont -> Token list -> Line -> Ans 
  type FailCont = Line -> Ans
  type 'a SuccCont = 'a -> FailCont -> Token list -> Line -> Ans 

*)

let runParser p str = (force p) (fun a fc tl ln -> ParseSuccess(a,tl)) (fun ln -> ParseFail(ln)) str 0;;

(* return: 'a -> 'a parser *)
let return x = lazy (fun sc -> sc x) ;;
  
(* fail : 'a parser *)
let fail = lazy (fun sc fc ts n -> fc n) ;;

(* bind : 'a parser -> ('a -> 'b parser) -> 'b parser *)
let bind p f = lazy (fun sc -> (force p) (fun x -> (force (f x)) sc));;


(* alt : 'a parser -> 'a parser -> 'a parser *)
let alt p q  =
  lazy
    (fun sc fc ts n -> 
     let fcp np = (force q) sc (fun nq -> fc (max np nq)) ts n
     in (force p) sc fcp ts n)
;;	  
  
(* any : Token parser *)
let any = lazy (fun sc fc ts n -> 
		match ts with
		| Nil -> fc n
		| Cons(t,ts') -> sc t fc ts' S(n))
;;			

let eos = lazy (fun sc fc ts n ->
		match ts with
		| Nil -> sc Unit fc ts n
		| Cons(t,ts') -> fc n)
;;	       
  
  
  
(* seq : ('a -> 'b -> 'c) -> 'a parser -> 'b parser -> 'c parser *)  
let seq f p q = bind p (fun a -> bind q (fun b -> return (f a b)));;
	       
(* bind : 'a parser -> 'b parser -> 'b parser *)  
let bind' p q = bind p (fun x -> q);;

(* filter : 'a parser -> ('a -> bool) -> 'a parser *)
let filter p f = bind p (fun x ->
			 match f x with
			 | True -> return x
			 | False -> fail)
;;
  
(* char : char -> char parser *)
let char c = filter any (eqChar c)
;;

let rec string cs =
  match cs with
  | Nil -> return Unit
  | Cons(c,cs') -> bind' (char c) (string cs')
;;

(* maybe :: 'a parser -> ('a option) parser   *)
let maybe p =
  let someP = bind p (fun r -> return Some(r)) 
  in alt someP (return None)
;;
  

(* promote : 'a parser parser -> 'a parser *)
let promote p = bind p (fun q -> q)  
;;
	     
let parser = bind' (char A) (bind' (char B) eos)
;;

let main input = runParser parser input
;;  
		 
