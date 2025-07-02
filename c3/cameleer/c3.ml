(*@ predicate rec distinct (l: 'a list) =
    forall i j. 0 <= i < List.length l -> 0 <= j < List.length l -> 
    i <> j -> Sequence.get l i <> Sequence.get l j*)

module type CLASS = sig

  type t


  (*@ function get_parents (x : t) (l : t list) : t list *)


  val eq : t -> t -> bool
  (*@ b = eq x y
        ensures b <-> x = y *)

  val get_parents : t -> t list -> t list
  (*@ l = get_parents c u
    requires distinct u
    requires Sequence.mem c u
    ensures not (List.mem c l)
    ensures distinct l
    ensures forall i. Sequence.mem i l -> Sequence.mem i u
  *)
  val to_string : t -> string

end

module Make(C : CLASS) = struct

  (*@ lemma list_seq_mem:
          forall l: C.t list, e:C.t.
          List.mem e l <-> Sequence.mem e l *)

  
  (*@ function rec sum_lengths (ll : C.t list list): int =
  match ll with 
  | [] -> 0
  | h::t -> (List.length h) + sum_lengths t
  *)

  (*@ predicate is_removed (l : C.t list) (r : C.t list) (e: C.t) =
    match l with 
    | [] -> [] = r
    | h::t -> 
      if h = e then t = r
      else l = r
    *)

  (*@ function lins_removed (ll: C.t list list) (h: C.t) : C.t list list =
    match ll with
    | [] -> []
    | l::rest -> (remove_head h l)::(lins_removed rest h)
  *)

  (*@ function remove_head (h: C.t) (l: C.t list) : C.t list =
    match l with
    | [] -> []
    | hd::tl -> if hd = h then tl else hd::tl
  *)

  (*@ predicate is_lins_removed (ll : C.t list list) (r : C.t list list) (e: C.t) =
      List.length ll = List.length r /\
      forall i. 0 <= i < List.length ll -> is_removed (Sequence.get ll i) (Sequence.get r i) e
  *)
  

 
  (*@ predicate has_head (a: C.t list) (e: C.t) = 
    match a with  
    |[] -> false
    |h::_ -> h = e*)

  (*@ function tail (l: C.t list): C.t list = 
    match l with 
    |[] -> []
    |_::t -> t*)

  (*@ predicate is_candidate_valid (c: C.t) (lins: C.t list list) =
      (forall j. 0 <= j < List.length lins -> 
        let lin = Sequence.get lins j in
        lin = [] \/ forall h1 t1. h1::t1 = lin -> h1 = c \/ not (Sequence.mem c t1)) *)


  (*@ lemma is_removed_not_mem:
  forall l: C.t list, r: C.t list , e: C.t.
    (is_removed l r e) /\ not (List.mem e (tail l)) -> not (List.mem e r)*)
    
  (*@ lemma is_removed_length_for_lists:
    forall l: C.t list list, r: C.t list list, e: C.t.
      ((List.length r = List.length l) /\
        (forall i. 0 <= i < List.length l -> is_removed (Sequence.get l i) (Sequence.get r i) e)) ->
          (forall i. 0 <= i < List.length l -> List.length (Sequence.get r i) <= List.length (Sequence.get l i))
  *)

  (*@ lemma sum_lengths_of_lists_l_e:
    forall l: C.t list list, r: C.t list list.
      ((List.length l = List.length r) /\
      (forall i. 0 <= i < List.length l -> List.length (Sequence.get r i) <= List.length (Sequence.get l i))) -> sum_lengths r <= sum_lengths l *)

  
  (*@ lemma sum_lengths_of_lists_l:
    forall l: C.t list list, r: C.t list list.
      ((List.length l = List.length r) /\
      (exists i. 0 <= i < List.length l /\ List.length (Sequence.get r i) < List.length (Sequence.get l i)) /\
      (forall i. 0 <= i < List.length l -> List.length (Sequence.get r i) <= List.length (Sequence.get l i))) -> sum_lengths r < sum_lengths l *)
  
  (*@ lemma sum_lengths_is_positive:
      forall ll: C.t list list.
      0 <= sum_lengths ll*)

  (*@ lemma is_removed_preserves_distinct:
        forall l r: C.t list, e: C.t.
        distinct l -> is_removed l r e -> distinct r *)
  
  (*@ lemma is_valid_on_tail:
        forall lins: C.t list list, l: C.t list.
          forall c. List.mem c l /\ is_candidate_valid c lins ->  
          forall e. List.mem e l /\ not is_candidate_valid e lins -> e <> c*)
  
  (*@ predicate rec is_lins_valid (lins: C.t list list) =
    (forall lin. Sequence.mem lin lins -> lin = []) ||
    exists lin h t. Sequence.mem lin lins /\ h::t = lin /\ is_candidate_valid h lins /\ 
    let new_lins = lins_removed lins h in
    sum_lengths lins > sum_lengths new_lins /\
    is_lins_valid new_lins    
  *)
  (*@ variant (sum_lengths lins) *)

  (* List.for_all *)
  let rec for_all f l =
    match l with
    | [] -> true
    | h::t -> f h && for_all f t
  (*@ r = for_all f l
    ensures r = (forall x. List.mem x l -> f x)
    variant l
  *)

  let rec filter_heads (l: C.t list list) =
    match l with
    | [] -> []
    | (h :: _) :: t -> h :: filter_heads t
    | [] :: t -> filter_heads t
  (*@ r = filter_heads l
    ensures forall y. List.mem y r -> (exists x h t. List.mem x l /\ h::t = x /\ h = y)
    ensures forall x h t. List.mem x l /\ x = h::t -> (exists y. List.mem y r /\ h = y)
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
      requires forall e. Sequence.mem e l -> distinct e
      
      ensures r <> []
      ensures forall i. 0 <= i < List.length r -> not (has_head (Sequence.get r i) e)
      
      ensures List.length l = List.length r
      ensures forall i : int. 0 <= i < List.length l -> is_removed (Sequence.get l i) (Sequence.get r i) e

      variant  l *)
  let remove (l: C.t list list) (e: C.t) : C.t list list =
    remove_aux l e
  (*@ r = remove l e
    requires l <> []
    requires  forall i. 0 <= i < List.length l -> distinct (Sequence.get l i)
    requires exists i. 0 <= i < List.length l /\ has_head (Sequence.get l i) e 
    requires forall i. 0 <= i < List.length l -> not (List.mem e (tail (Sequence.get l i)))
    
    ensures forall i. 0 <= i < List.length r -> not (List.mem e (Sequence.get r i))
    ensures forall i. Sequence.mem i r -> distinct i
    ensures sum_lengths r < sum_lengths l
    ensures r <> []
  *)
  
   

  let rec merge (linearizations : C.t list list) : C.t list  =
    if for_all ((fun l -> List.length l = 0)) linearizations then []
    else
      
      let find_candidate () =
        let heads = filter_heads linearizations 
        in 
        let rec try_heads (l: C.t list) = match (l: C.t list) with
          | [] -> assert false  
          | candidate :: rest ->
              let is_valid = for_all 
                (fun l -> 
                  match (l : C.t list) with
                  | [] -> true
                  | h::t -> C.eq h candidate || not (List.mem candidate t))
                linearizations in
              
              if is_valid then candidate
              else try_heads rest
        (*@ r = try_heads l
        variant l 
        requires forall i. List.mem i l -> (exists j h t. List.mem j linearizations /\ h::t = j /\ h=i )
        ensures (exists j. List.mem j linearizations /\ (has_head j r) ) 
        requires exists c. Sequence.mem c l /\ is_candidate_valid c linearizations*)
        in
        try_heads heads
      (*@ r = find_candidate ()
      ensures is_candidate_valid r linearizations*)
      in
      
      
      let candidate = find_candidate () in
      let merged = merge (remove linearizations candidate) in
      candidate :: merged
  (*@ l = merge lins
        requires lins <> []
        requires forall i. Sequence.mem i lins -> distinct i
        requires is_lins_valid lins

        ensures distinct l
        ensures forall ia ib. 0 <= ia < ib < List.length l ->
          let ea = Sequence.get l ia in
          let eb = Sequence.get l ib in 
          exists ja jb lin.  
            Sequence.mem lin lins /\ ea = Sequence.get lin ja /\ eb = Sequence.get lin jb /\ ja < jb
        ensures forall e. not (Sequence.mem e l) -> forall lin. Sequence.mem lin lins -> not (Sequence.mem e lin) 
        ensures forall lin e. (Sequence.mem lin lins) /\ not (Sequence.mem e lin) -> not (Sequence.mem e l)
        ensures forall e. Sequence.mem e l -> exists lin. (Sequence.mem lin lins) /\ (Sequence.mem e lin) 
        variant sum_lengths lins
  *)  

              

  let c3_linearization (universe: C.t list) (c: C.t)  =

    let rec linearize (universe: C.t list) (c: C.t) : C.t list * C.t list list =
        let parents = C.get_parents c universe in
        if (List.length universe) = 0 || (List.length parents) = 0 then
          ([c],[[c]])
        else
            let rec remove_c l =
              match l with
              | [] -> []
              | x :: xs -> if C.eq x c then remove_c xs else x :: remove_c xs
              (*@ r = remove_c l
                requires distinct l
                ensures not (Sequence.mem c r)
                ensures forall i. 0 <= i < List.length r -> Sequence.mem (Sequence.get r i) l
                ensures forall i. 0 <= i < List.length l /\ ((Sequence.get l i) <> c) -> Sequence.mem (Sequence.get l i) r 
                ensures distinct r
                variant l*)
            in
            let universe' = remove_c universe in
          if (List.length universe) = (List.length universe') then
            assert false
          else
            let rec parent_linearizations ps : C.t list list = 
              match ps with 
              |[] -> []
              |h::t -> let lin, _ = linearize universe' h in lin :: (parent_linearizations t)
            (*@ r = parent_linearizations ps
               
              requires forall x. Sequence.mem x ps -> Sequence.mem x universe'
              requires distinct ps
              ensures List.length r = List.length ps
              ensures forall i. 0 <= i < List.length r -> distinct (Sequence.get r i)
              ensures forall i. 0 <= i < List.length ps -> (forall h t. h::t = (Sequence.get r i) -> h = (Sequence.get ps i))
              ensures forall c. not (Sequence.mem c universe') -> forall l. Sequence.mem l r -> not (Sequence.mem c l)  
              
              ensures forall l c. Sequence.mem l r /\ Sequence.mem c l -> Sequence.mem c universe
              
              ensures is_lins_valid r
              ensures is_lins_valid (List.append r (ps::[]))
              
            
              variant ps
            *)
        
            in
            let linearizations = (parent_linearizations parents) @ [parents] in
            (c :: (merge linearizations), linearizations) 
    (*@ r, lins = linearize uni c
          requires distinct uni
          requires Sequence.mem c uni
          ensures forall e. Sequence.mem e r -> Sequence.mem e uni
          variant List.length uni
          ensures forall h t. h::t = r -> h = c /\ not (Sequence.mem h t)
          ensures distinct r
          *)
    in

    
    linearize universe c

  (*@ li = c3_linearization uni c
      requires distinct uni 
      requires Sequence.mem c uni
  *)  
end
