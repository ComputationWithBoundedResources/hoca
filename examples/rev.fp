let rec append xs ys = 
  match xs with 
  | Nil -> ys
  | Cons(x,xs') -> Cons(x, append xs' ys) 
in
let rec rev xs =
  match xs with 
  | Nil -> Nil
  | Cons(x,xs') -> append (rev xs') Cons(x,Nil)
in fun l -> rev l
