let rec even x =
  match x with
  | 0 -> True
  | S(x') -> odd x'
and odd x = 
  match x with
  | 0 -> False
  | S(x') -> even x'
in fun x -> even x
