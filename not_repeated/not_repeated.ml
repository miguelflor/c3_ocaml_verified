module type EQUAL = sig
  type t

  val eq : t -> t -> bool
  (*@ b = eq x y
    ensures b <-> x = y *) 

end

module Set (E : EQUAL) = struct

type set = E.t list


val empty = [] 

val add (t: E.t) (s : set) =  x :: s

end

