let id x = x
in let comp f g x = f (g x)
in let cons x xs = Cons(x,xs)
in let rec walk l = 
  match l with 
  | Nil -> id
  | Cons(x,xs) -> comp (walk xs) (cons x)
in fun l -> walk l Nil
