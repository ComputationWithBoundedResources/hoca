let pred x = match x with
  | S(y) -> y
  | 0 -> 0
in fun x -> pred x
