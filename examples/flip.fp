let rec flip x = 
  match x with
  | E -> E
  | Z(x') -> O(flip x')
  | O(x') -> Z(flip x')
;;


    
