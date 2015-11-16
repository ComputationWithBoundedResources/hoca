let rec max x y =
  match x with
  | 0 -> y
  | S(x') ->
     match y with
     | 0 -> x
     | S(y') -> S(max x' y')
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
let bind2 p f = lazy (fun sc -> (force p) (fun x -> (force (f x)) sc));;
let bind3 p f = lazy (fun sc -> (force p) (fun x -> (force (f x)) sc));;  
  

(* alt : 'a parser -> 'a parser -> 'a parser *)
let alt p q  =
  lazy
    (fun sc fc ts n -> 
     let alt_fail np = (force q) sc (fun nq -> fc (max np nq)) ts n
     in (force p) sc alt_fail ts n)
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
  
  
(* filter : 'a parser -> ('a -> bool) -> 'a parser *)
let filter p f = bind p (fun x ->
			 match f x with
			 | True -> return x
			 | False -> fail)
;;
  
(* char : char -> char parser *)
let char c = filter any (eqChar c)
;;

(* promote : 'a parser parser -> 'a parser *)
let promote p = bind2 p (fun q -> q)  
;;

let rec pas p =
  alt (bind (char A) (fun a -> pas (bind3 (char B) (fun x -> p))))
      (return p)
;;

let parser = promote (pas eos);;

let main input = runParser parser input
;;  
		 
