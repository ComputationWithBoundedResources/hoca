let cons x xs = Cons(x,xs)
in let comp f g x = f (g x)
in let rec walk t = 
  match t with 
  | Leaf(x) -> cons x
  | Node(t1,t2) -> comp (walk t1) (walk t2)
in fun t -> walk t Nil

