module type CLASS = sig

  type t

  (*@ predicate eq (x:t) (y:t)*)

  (*@ function getParents (x : t) : t list *)


  val eq : t -> t -> bool
  (*@ b = eq x y
        ensures b <-> eq x y *)

  val getParents : t -> t list
  (*@ l = getParents c
    ensures l = getParents c 
    ensures not (List.mem c l)*)

  val to_string : t -> string

end

module Make(C : CLASS) = struct
  

  (* List.for_all *)
  let rec for_all f l =
    match l with
    | [] -> true
    | h::t -> f h && for_all f t
  (*@ r = for_all f l
    ensures r = (forall x. List.mem x l -> f x)
    variant l
  *)
  
  (* List.filter_map *)
  let rec filter_map f l =
  match l with
  | [] -> []
  | h::t ->
      match f h with
      | None -> filter_map f t
      | Some x -> x :: filter_map f t
  (*@ r = filter_map f l
    ensures forall y. List.mem y r <-> (exists x. List.mem x l /\ f x = Some y)
    variant l
  *)

  (*finds and drops*)
  (*let find_and_drop (p: C.t) (lst: C.t list) =
    let rec aux (acc: C.t list) (p: C.t) (lst: C.t list) = 
      match lst with
      | [] -> acc
      | h::t -> 
        if C.eq h p then acc @ t
        else aux (acc@[h]) p t 
      in aux [] p lst*)
  
  (* Removes from a list of lists of classes (l) an element (e) *)
  let remove (l: C.t list list) (e: C.t) : C.t list list = 
    List.map
    (fun l -> List.filter (fun x -> not (C.eq x e)) l)
    l 
  (*@ r = remove l e
    ensures forall y. List.mem y l -> not (List.mem e y)*)
  
   

  let rec merge (linearizations : C.t list list) : C.t list option  =
    if for_all ((fun l -> List.length l = 0)) linearizations then Some []
    else
      
      let find_candidate () =
        let heads = filter_map 
          (fun (l: C.t list) -> match (l: C.t list) with
            | [] -> None 
            | h::_ -> Some h) 
          linearizations in
        
        let rec try_heads (l: C.t list) = match (l: C.t list) with
          | [] -> None  
          | candidate :: rest ->
              let is_valid = for_all 
                (fun l -> 
                  match (l : C.t list) with
                  | [] -> true
                  | h::t -> C.eq h candidate || not (List.mem candidate t))
                linearizations in
              
              if is_valid then Some candidate
              else try_heads rest
        (*@ variant l*)
        in
        try_heads heads
      in
      
      match find_candidate () with
      | None -> None
      | Some candidate -> 
        match merge (remove linearizations candidate) with
        |None -> None
        |Some l -> Some (candidate :: l)
  (*@ l = merge lins
        ensures match l with
        |None -> not (exists k. List.mem k lins -> 
          match k with 
            | h::t -> forall i. List.mem i lins -> not (List.mem h t)
            | [] -> false
          )
        |Some _ -> true

        variant List.length lins
  *)    
              

  let c3_linearization (universe: C.t list) (c: C.t)  =

    let rec linearize (universe: C.t list) (c: C.t) : C.t list option  =
        let parents = C.getParents c in
        if (List.length universe) = 0 || (List.length parents) = 0 then
          Some [c]
        else
          let universe' = List.filter (fun x -> not (C.eq x c)) universe in
          if (List.length universe) = (List.length universe') then
            None
          else
            let parent_linearizations  = List.map (linearize universe') parents in
            let parent_linearizations' = filter_map (fun x -> x)  parent_linearizations in

            if (List.length parent_linearizations) = (List.length parent_linearizations') then
              let linearizations = parent_linearizations' @ [parents] in
              match merge linearizations with
              |Some l -> Some (c :: l)
              |None -> None
            else
              None
    (*@ r = linearize uni c
          ensures 
          match r with
          |None -> not (forall x. List.mem x (C.getParents c) -> List.mem x uni)
          |Some _ -> true

          requires List.mem c uni
          variant List.length uni
          *)
    in

    
    match linearize universe c with
    |Some x -> x
    |None -> invalid_arg "Universe is not properly created"

  (*@ li = c3_linearization uni c
      raises Invalid_argument _ -> not (List.mem c uni) \/ not (forall x. List.mem x (C.getParents c) -> List.mem x uni)
      requires List.mem c uni
  *)  
end
