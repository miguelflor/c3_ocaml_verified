open Types


let object_class = Class("O", [])
let a_class = Class("A", [object_class])
let b_class = Class("B", [object_class])
let c_class = Class("C", [object_class])
let d_class = Class("D", [object_class])
let e_class = Class("E", [object_class])
let k1_class = Class("K1", [c_class; a_class; b_class])
let k3_class = Class("K3", [a_class; d_class])
let k2_class = Class("K2", [b_class; d_class; e_class])
let z_class = Class("Z", [k1_class; k3_class; k2_class])


let () =
  match C3.c3 z_class with
    | Ok mro -> Printf.printf "%s\n" (String.concat " -> " mro)
      
    | Error msg -> 
        Printf.printf "Error: %s\n" msg

(*[Z, K1, C, K3, A, K2, B, D, E, O, <class 'object'>]*)    
(*return*)  
(*Z -> K1 -> C -> K3 -> A -> K2 -> B -> D -> E -> O*)
