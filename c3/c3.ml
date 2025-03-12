type class_name = string
type class_hierarchy = (class_name * class_name list) list

let get_parents hierarchy class_name =
  match List.assoc_opt class_name hierarchy with
  | Some parents -> parents
  | None -> []

let rec merge linearizations =
  if List.for_all (fun l -> l = []) linearizations then []
  else
    let find_candidate () =
      let heads = List.filter_map 
        (function [] -> None | h::_ -> Some h) 
        linearizations in
      
      let rec try_heads = function
        | [] -> None  
        | candidate :: rest ->
            let is_valid = List.for_all 
              (fun l -> 
                match l with
                | [] -> true
                | h::t -> h = candidate || not (List.mem candidate t))
              linearizations in
            
            if is_valid then Some candidate
            else try_heads rest
      in
      try_heads heads
    in
    
    match find_candidate () with
    | None -> failwith "Cannot create a consistent linearization"
    | Some candidate ->
        let updated_linearizations = List.map
          (function
            | [] -> []
            | h::t -> if h = candidate then t else h::t)
          linearizations in
        
      candidate :: merge updated_linearizations

let c3_linearization hierarchy class_name =
  let rec linearize class_name =
    let parents = get_parents hierarchy class_name in
  
    let parent_linearizations = List.map linearize parents in
    
    let linearizations = parent_linearizations @ [parents] in
    
    class_name :: merge linearizations
  in
  
  linearize class_name


let () =
  
  let hierarchy = [
    ("O", []);                
    ("A", ["O"]);             
    ("B", ["O"]);             
    ("C", ["O"]);             
    ("D", ["O"]);             
    ("E", ["O"]);             
    ("K1", ["A"; "B"; "C"]);  
    ("K2", ["D"; "B"; "E"]);  
    ("K3", ["D"; "A"]);       
    ("Z", ["K1"; "K2"; "K3"]) 
  ] in
  
  let z_linearization = c3_linearization hierarchy "Z" in
  
  Printf.printf "C3 linearization of Z: %s\n" 
    (String.concat " -> " z_linearization)