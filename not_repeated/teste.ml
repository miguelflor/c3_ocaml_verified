(*@ open Set *)

let rec not_in_list (x : int) (l : int list) =
  match l with
  | [] -> true
  | y :: r -> x <> y && not_in_list x r 

let rec not_repeated (l: int list) = 
  match l with
      | [] -> true
      | x :: r -> not_in_list x r && not_repeated r
(*@
  r = not_repeated l
  ensures (Set.cardinal (Set.of_list l) = (List.length l)) = r
  *) 


