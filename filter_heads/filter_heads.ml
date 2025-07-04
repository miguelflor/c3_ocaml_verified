let rec filter_heads (l: 'a list list) =
    match l with
    | [] -> []
    | (h :: _) :: t -> h :: filter_heads t
    | [] :: t -> filter_heads t
  (*@ r = filter_heads l
    ensures forall y. List.mem y r -> 
      (exists x h t. List.mem x l /\ h::t = x /\ h = y)
    ensures (forall x h t. List.mem x l /\ x = h::t -> List.mem h r)
    variant l
  *)