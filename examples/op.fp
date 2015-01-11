  
(* 
  type 'a parser = 'a SuccCont -> FailCont -> Token list -> Line -> Ans 
  type FailCont = Line -> Ans
  type 'a SuccCont = 'a -> FailCont -> Token list -> Line -> Ans 

*)

let runParser p str = p (fun a fc ts ln -> ParseSuccess(a,ts)) (fun ln -> ParseFail(ln)) str 0;;

(* any : Token parser *)
let any sc fc ts n = 
  match ts with
  | Nil -> fc n
  | Cons(t,ts') -> sc t fc ts' n
;;			

  
  runParser any input
