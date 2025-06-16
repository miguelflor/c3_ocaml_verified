module type CLASS = sig

  type t

  (* @ predicate eq (x:t) (y:t)*)

  (*@ function get_parents (x : t) : t list *)


  val eq : t -> t -> bool
  (*@ b = eq x y
        ensures b <-> x = y *)

  val get_parents : t -> t list
  (*@ l = get_parents c
    ensures l = get_parents c 
    ensures not (List.mem c l)*)

  val to_string : t -> string

end

module Make(C : CLASS) = struct
  
  
  (*@ function rec sum_lengths (ll : C.t list list): int =
  match ll with 
  | [] -> 0
  | h::t -> (List.length h) + sum_lengths t
  *)
  
  (*@ predicate is_removed (a : C.t list) (b : C.t list) (e: C.t) =
    match a with 
    | [] -> [] = b
    | h::t -> 
      if h = e then t = b 
      else a = b
    *)

    (*@ predicate has_head (a: C.t list) (e: C.t) = 
    match a with 
    |[] -> false
    |h::_ -> h = e*)

    (*@ function tail (l: C.t list): C.t list = 
    match l with 
    |[] -> []
    |_::t -> t*)
    
    (*@ predicate rec distinct (l: C.t list) =
    match l with
    |[] -> true
    |h::t -> not (List.mem h t) /\ distinct t*)
    
    (*@ predicate rec is_mapped_by_remove (a : C.t list list) (b : C.t list list) (e: C.t) =
    match a,b with
    |[],[] -> true
    |[],_ -> false
    |_,[] -> false
    |ha::ta,hb::tb -> is_removed ha hb e /\ is_mapped_by_remove ta tb e*)
    
    (*@ lemma list_must_eq_dec: forall x:C.t list,y:C.t list,e:C.t. is_removed x y e -> List.length x >= List.length y*)
    
    (*@ lemma list_must_dec: forall x:C.t list, y:C.t list,e:C.t. is_removed x y e -> 
      match x with
      |[] -> List.length x = List.length y
      |h::_ -> 
        if h = e then List.length x > List.length y
        else List.length x = List.length y*)
    
    (* @ lemma lists_must_dec_l: forall x: C.t list list, y: C.t list list,l: C.t list, e : C.t. (is_mapped_by_remove x y e /\ not (List.mem l x) /\ (List.mem l y) )-> List.mem (e::l) x *)


    (* @ lemma lists_must_dec: forall x: C.t list list, y: C.t list list, e : C.t. 
    (List.length x = List.length y /\ is_mapped_by_remove x y e /\ (forall i: int. 0 < i < List.length x -> (Seq.get x i) = (Seq.get y i) \/ (Seq.cons e (Seq.get y i)) = (Seq.get x i))) -> sum_lengths x > sum_lengths y *)
    
    
    (*@ lemma lists_must_dec: forall x: C.t list list, y: C.t list list, e : C.t. 
    (List.length x = List.length y /\
    is_mapped_by_remove x y e)
    -> forall i: int. 0 < i < List.length x -> (Seq.get x i) = (Seq.get y i) \/ (Seq.cons e (Seq.get y i)) = (Seq.get x i) *)
    
    
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

  let remove_head (x: C.t) (l: C.t list) : C.t list =
    match l with
    | [] -> []
    | y :: r -> if C.eq x y then r else y :: r
  (*@ r = remove_head x l
      requires distinct l
      ensures is_removed l r x
  *)
  
  (* Removes from a list of lists of classes (l) an element (e) *)
  let rec remove_aux (l: C.t list list) (e: C.t) : C.t list list =
    match l with
    | [] -> assert false
    | [a] -> [remove_head e a]
    | a :: r -> remove_head e a :: remove_aux r e
  (*@ r = remove l e
      requires l <> []
      requires  forall y. List.mem y l -> distinct y

      ensures r <> []
      ensures forall a. List.mem a r -> forall x y. a = x :: y -> x <> e 

      ensures forall a. List.mem a l -> exists b. List.mem b r /\ is_removed a b e
      ensures forall b. List.mem b r -> exists a. List.mem a l /\ is_removed a b e
      
      ensures  is_mapped_by_remove l r e

      variant  l *)
  let remove (l: C.t list list) (e: C.t) : C.t list list =
    remove_aux l e
  (*@ r = remove l e
    requires l <> []
    requires  forall y. List.mem y l -> distinct y
    requires exists a. List.mem a l /\ has_head a e 
    requires forall a. List.mem a l -> forall x y. a = x :: y -> not List.mem e y
    
    ensures forall y. List.mem y r -> not (List.mem e y)
    ensures sum_lengths r < sum_lengths l
  *)
  
   

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
        |None -> not (exists k. List.mem k lins /\
          match k with 
            | h::t -> forall i. List.mem i lins -> not (List.mem h t)
            | [] -> false
          )
        |Some _ -> true

        variant sum_lengths lins
  *)    
              

  let c3_linearization (universe: C.t list) (c: C.t)  =

    let rec linearize (universe: C.t list) (c: C.t) : C.t list option  =
        let parents = C.get_parents c in
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
          |None -> not (forall x. List.mem x (C.get_parents c) -> List.mem x uni)
          |Some _ -> true

          requires List.mem c uni
          variant List.length uni
          *)
    in

    
    match linearize universe c with
    |Some x -> x
    |None -> invalid_arg "Universe is not properly created"

  (*@ li = c3_linearization uni c
      raises Invalid_argument _ -> not (List.mem c uni) \/ not (forall x. List.mem x (C.get_parents c) -> List.mem x uni)
      requires List.mem c uni
  *)  
end
