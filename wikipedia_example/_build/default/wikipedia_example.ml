open Featherweightsolidity

(* Now you can access C3 module functions *)
module Types = struct
  type 'a hierarchy = Class of 'a * 'a hierarchy list
  
  type contract_def = {
    super_contracts: string hierarchy;
  }
end

open Types

(* Define the Wikipedia example class hierarchy *)
let object_class = Class("Object", [])
let a_class = Class("A", [object_class])
let b_class = Class("B", [object_class])
let c_class = Class("C", [a_class])
let d_class = Class("D", [b_class])
let e_class = Class("E", [c_class; d_class])

(* Create a contract definition *)
let wikipedia_example = {
  super_contracts = e_class;
}

(* Compute the C3 linearization *)
let () =
  match C3.c3 e_class with
  | Ok mro -> 
      Printf.printf "C3 Linearization: %s\n" 
        (String.concat " -> " mro)
  | Error msg -> 
      Printf.printf "Error: %s\n" msg