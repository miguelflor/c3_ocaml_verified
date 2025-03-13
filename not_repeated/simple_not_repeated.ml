(*@ open Set *)

let (l1: int list) = ([1]:int list)
(*@
  r = l1
  ensures Set.singleton 9 = Set.add 9 Set.empty
  ensures Set.to_seq Set.empty = Sequence.empty
  *) 

let (l2: int list)  = ([]: int list)


let l3 = [1; 2; 3; 4; 7; 6; 8]
 