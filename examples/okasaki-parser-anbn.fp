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
(* let eqChar x y = *)
(*   match x with *)
(*   | SLASH -> (match y with  *)
(*            | SLASH -> True *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | LPAREN -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> True *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | RPAREN -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> True *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | DOT -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> True *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | GT -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> True *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | MINUS -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> True *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | SPACE -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> True *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | A -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> True *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | B -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> True *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | C -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> True *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | D -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> True *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | E -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> True *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | F -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> True *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | G -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> True *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | H -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> True *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | I -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> True *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | J -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> True *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | K -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> True *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | L -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> True *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | M -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> True *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | N -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> True *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | O -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> True *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | P -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> True *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | Q -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> True *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | R -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> True *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | S -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> True *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | T -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> True *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | U -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> True *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | V -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> True *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | W -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> True *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | X -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> True *)
(*            | Y -> False *)
(*            | Z -> False) *)
(*   | Y -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> True *)
(*            | Z -> False) *)
(*   | Z -> (match y with  *)
(*            | SLASH -> False *)
(*            | LPAREN -> False *)
(*            | RPAREN -> False *)
(*            | DOT -> False *)
(*            | GT -> False *)
(*            | MINUS -> False *)
(*            | SPACE -> False *)
(*            | A -> False *)
(*            | B -> False *)
(*            | C -> False *)
(*            | D -> False *)
(*            | E -> False *)
(*            | F -> False *)
(*            | G -> False *)
(*            | H -> False *)
(*            | I -> False *)
(*            | J -> False *)
(*            | K -> False *)
(*            | L -> False *)
(*            | M -> False *)
(*            | N -> False *)
(*            | O -> False *)
(*            | P -> False *)
(*            | Q -> False *)
(*            | R -> False *)
(*            | S -> False *)
(*            | T -> False *)
(*            | U -> False *)
(*            | V -> False *)
(*            | W -> False *)
(*            | X -> False *)
(*            | Y -> False *)
(*            | Z -> True) *)
(* ;; *)
	
let isAlphaChar x =
  match x with 
  | SLASH -> False
  | DOT -> False
  | MINUS -> False
  | GT -> False
  | LPAREN -> False
  | RPAREN -> False
  | SPACE -> False
  | A -> True
  | B -> True
  | C -> True
  | D -> True
  | E -> True
  | F -> True
  | G -> True
  | H -> True
  | I -> True
  | J -> True
  | K -> True
  | L -> True
  | M -> True
  | N -> True
  | O -> True
  | P -> True
  | Q -> True
  | R -> True
  | S -> True
  | T -> True
  | U -> True
  | V -> True
  | W -> True
  | X -> True
  | Y -> True
  | Z -> True
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

(* char : Char parser *)  
let alphaChar = filter any isAlphaChar
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
  
let rec many p =
  bind (maybe p)
       (fun ro ->
	match ro with
	| None -> return Nil
	| Some(r) -> bind (many p) (fun rs -> return Cons(r,rs)))
;;       
      
let many1 p = seq (fun r rs -> Cons(r,rs)) p (many p)
;; 

let followedBy p q = seq (fun rp rq -> rp) p q
;;			 
let lexeme p = bind p (fun r -> bind' (alt (char SPACE) (return SPACE)) (return r))
;;

let between pl pr p = bind' pl (bind p (fun r -> bind' pr (return r)))
;;			    
let parens = between (lexeme (char LPAREN)) (lexeme (char RPAREN))
;;		     

(* let rec pExp = *)
(*   let pVar = many1 alphaChar *)
(*   and pApp = *)
(*     seq (fun e1 e2 -> App e1 e2) (lexeme pExp) (lexeme pExp) *)
(*   and pAbs = *)
(*     bind' (lexeme (char SLASH)) *)
(* 	  (seq (fun v e -> Abs v e) *)
(* 	       (followedBy (lexeme pVar) (lexeme (char DOT))) *)
(* 	       (lexeme pExp)) *)
(*   in alt pVar (parens (alt pAbs pApp)) *)
(* ;; *)

(* promote : 'a parser parser -> 'a parser *)
let promote p = bind p (fun q -> q)  
;;

let rec pas p =
  bind (maybe (char A))
       (fun ma ->
	match ma with
	| Some(a) -> pas (bind' (char B) p)
	| None -> return p)
;;


let parser = promote (promote eos);;

  runParser parser input
		 
