let rec even x =
  let rec odd x =
    match x with
    | 0 -> False
    | S(x') -> even x'
  in match x with
     | 0 -> True
     | S(x') -> odd x'
in fun x -> even x 		    
