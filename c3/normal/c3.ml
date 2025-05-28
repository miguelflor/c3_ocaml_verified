module type CLASS = sig

  type t

  val eq : t -> t -> bool

  val getParents : t -> t list

  val to_string : t -> string

end

module Make(C : CLASS) = struct
  
  
  (*finds and drops*)
  let find_and_drop (p: C.t) (lst: C.t list) =
    let rec aux (acc: C.t list) (p: C.t) (lst: C.t list) = 
      match lst with
      | [] -> acc
      | h::t -> 
        if C.eq h p then acc @ t
        else aux (acc@[h]) p t 
      in aux [] p lst
  
  (* Removes from a list of lists of classes (l) an element (e) *)
  let remove (l: C.t list list) (e: C.t) : C.t list list = 
    List.map
    (fun l -> match l with
      | [] -> []
      | h::t -> if C.eq h e then t else h::t)
    l 
   

  let rec merge (linearizations : C.t list list) : C.t list  =
    if List.for_all ((fun l -> List.length l = 0)) linearizations then []
    else
      
      let find_candidate () =
        let heads = List.filter_map 
          (fun (l: C.t list) -> match (l: C.t list) with
            | [] -> None 
            | h::_ -> Some h) 
          linearizations in
        
        let rec try_heads (l: C.t list) = match (l: C.t list) with
          | [] -> None  
          | candidate :: rest ->
              let is_valid = List.for_all 
                (fun l -> 
                  match (l : C.t list) with
                  | [] -> true
                  | h::t -> C.eq h candidate || not (List.exists (fun x -> C.eq x candidate) t))
                linearizations in
              
              if is_valid then Some candidate
              else try_heads rest
        in
        try_heads heads
      in
      
      match find_candidate () with
      | None -> failwith "Cannot create a consistent linearization"
      | Some candidate -> candidate :: merge (remove linearizations candidate)
              

  let c3_linearization (c: C.t)  =
  
    let rec linearize (c: C.t) =
   
        let parents = C.getParents c in
      
        let parent_linearizations  = List.map linearize parents in

        let linearizations = parent_linearizations @ [parents] in

        c :: merge linearizations
    in
    linearize c

end
