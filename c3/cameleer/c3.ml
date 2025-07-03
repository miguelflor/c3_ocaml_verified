(*@ predicate distinct (l: 'a list) =
  forall i j. 0 <= i < j < List.length l -> Sequence.get l i <> Sequence.get l j *)

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
 
    (*@ predicate has_head (a: C.t list) (e: C.t) = 
    a <> [] /\
    forall h t. h::t = a-> e = h
    *)

    (*@ function tail (l: C.t list): C.t list = 
    match l with 
    |[] -> []
    |_::t -> t*)

    (*@ predicate is_epg (l: C.t list list) =
      forall i1:int, i2:int.
      0 <= i1 /\ i1 < List.length l ->
      0 <= i2 /\ i2 < List.length l ->
      i1 <> i2 ->
      (let l1 = Sequence.get l i1 in
        let l2 = Sequence.get l i2 in
        forall e1:C.t, e2:C.t, i11:int, i21:int, j1:int, j2:int.
        Sequence.get l1 i11 = e1 /\
        Sequence.get l1 i21 = e2 /\
        Sequence.get l2 j1 = e1 /\
        Sequence.get l2 j2 = e2 /\ i11 < i21 ->
        j1 < j2)*)
    
    (*@ predicate acyclic_precedence_graph (lins: C.t list list) =
      forall c.
        not (
          exists path: C.t list.
            List.length path > 1 /\
            Sequence.get path 0 = c /\
            Sequence.get path (List.length path - 1) = c /\
            (forall i.
              0 <= i /\ i < (List.length path) - 1 ->
                exists lin: C.t list, j.
                  List.mem lin lins /\
                  List.length lin > 1 /\
                  0 <= j /\ j < (List.length lin) - 1 /\
                  Sequence.get lin j = Sequence.get path i /\
                  Sequence.get lin (j+1) = Sequence.get path (i+1)
            )
        ) *)

    (*@ predicate is_candidate_valid (c: C.t) (lins: C.t list list) =
      (forall j. Sequence.mem j lins -> 
        match j with
        | [] -> true
        | h1::t1 -> h1 = c \/ not (List.mem c t1))  *)
    

    (* other lemmas *)

    (*@ lemma list_seq_mem:
          forall l: C.t list, e:C.t.
          List.mem e l <-> Sequence.mem e l *)

    (*@ lemma head_is_at_index_zero:
      forall l: C.t list, a: C.t, i: int.
        has_head l a /\ distinct l /\ a = Sequence.get l i -> i = 0 *)

    (*@ lemma tail_is_above_zero:
      forall l,t: C.t list, a,h: C.t, i: int.
        List.length l > 1 /\ h::t = l /\
        Sequence.mem a t /\ distinct l /\ a = Sequence.get l i -> i > 0 *)
    
    (* remove lemmas *)

    (*@ lemma is_removed_not_mem:
    forall l: C.t list, r: C.t list , e: C.t.
      (is_removed l r e) /\ not (List.mem e (tail l)) -> not (List.mem e r)*)

    (*@ lemma is_removed_length:
      forall l: C.t list, r: C.t list, e: C.t.
        (is_removed l r e /\ has_head l e) ->
        (List.length r < List.length l)*)
      
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
    
    (*@ lemma is_candidate_on_distinct:
          forall lins: C.t list list, c: C.t.
            (forall i. 0 <= i < List.length lins -> distinct (Sequence.get lins i)) /\ is_candidate_valid c lins ->
              (forall i. 0 <= i < List.length lins -> not (List.mem c (tail (Sequence.get lins i))))*)

    (*@ lemma distinct_head_not_in_tail:
          forall l: C.t list.
          distinct l -> (forall h t. h::t = l -> (distinct t /\ not (Sequence.mem h t)))*)

    (*@ lemma length_strictly_decreases_if_element_removed:
          forall l1 l2: C.t list, e:C.t.
            distinct l1 /\ distinct l2 /\ Sequence.mem e l1 /\ not (Sequence.mem e l2) /\
            (forall x. Sequence.mem x l2 -> Sequence.mem x l1) /\ 
            (forall x. Sequence.mem x l1 /\ x <> e -> Sequence.mem x l2) ->
            List.length l2 < List.length l1*)
 
    (* candidate lemmas *)

    (*@ lemma in_list_not_in_head_must_be_in_tail:
      forall lins: C.t list list.
        (forall p t h. h::t = p /\ 
        (exists c. Sequence.mem c p /\ is_candidate_valid c lins) /\ 
        (not is_candidate_valid h lins) -> (exists c. Sequence.mem c t /\ is_candidate_valid c lins))
      *)
    
    (*@ lemma candidate_is_only_head:
      forall lins: C.t list list, a :C.t.
      (forall lin. Sequence.mem lin lins -> distinct lin ) /\ 
      (exists lin h t. Sequence.mem lin lins /\ h::t = lin /\ h = a) /\ 
      is_candidate_valid a lins -> (forall lin h t. (Sequence.mem lin lins /\ Sequence.mem a lin /\ h::t = lin) -> (h = a /\ (forall i. a = Sequence.get lin i -> i = 0 ))) 
    *)

    (*@ lemma candidate_is_always_first:
      forall lins: C.t list list, a :C.t.
      (forall lin. Sequence.mem lin lins -> distinct lin ) /\ (exists lin h t. Sequence.mem lin lins /\ h::t = lin /\ h = a) /\ is_candidate_valid a lins ->
        (forall lin,k,ai,ki. (Sequence.mem lin lins /\ Sequence.mem a lin /\ Sequence.mem k lin /\ a = Sequence.get lin ai /\ k = Sequence.get lin ki /\ a <> k) -> ai < ki) *)
   
    (* order lemma *)

     (*@ lemma if_linearization_is_possible_is_acyclic:
        forall lins: C.t list list.
        (acyclic_precedence_graph lins)  -> (exists path. List.length path > 1 /\ distinct path /\ (
          forall lin. Sequence.mem lin lins ->
            forall i j. 0 <= i < j <= List.length lin ->
              let ei = Sequence.get lin i in
              let ej = Sequence.get lin j in
              (exists ip jp. ei = Sequence.get path ip  /\ ej = Sequence.get path jp /\ ip < jp )
        ))  *)

     (*@ lemma acyclic_is_ordered:
          forall lins: C.t list list.
          is_epg lins -> acyclic_precedence_graph lins*)

     (*@ lemma acyclic_has_head_candidate:
        forall lins: C.t list list, c: C.t.
         acyclic_precedence_graph lins -> (exists lin h t. Sequence.mem lin lins /\ Cons h t = lin /\ is_candidate_valid h lins)
          *)
      
      (*@ lemma acyclic_and_has_candidate:
      forall lins: C.t list list, c:C.t.
        ((exists lin. Sequence.mem lin lins /\ lin <> []) /\ acyclic_precedence_graph lins /\
        is_candidate_valid c lins) -> (exists lin h t. Sequence.mem lin lins /\ h::t = lin /\ h = c)
          
      *)

      (*@ lemma remove_preserves_order:
      forall ls lsr: C.t list list, r:C.t.
        (List.length ls = List.length lsr) ->
        (forall i. 0 <= i < List.length ls -> is_removed (Sequence.get ls i) (Sequence.get lsr i) r) /\ acyclic_precedence_graph ls -> 
          acyclic_precedence_graph lsr *)


    (* @ lemma epg_concat_with_list_of_unique_elements_is_epg:
          forall l: C.t list list, ps: C.t list.
            
            (forall e. Sequence.mem e l -> distinct e) /\ (distinct ps) /\ (is_epg l) /\ (List.length ps = List.length l) /\ 
            (forall p. Sequence.mem p ps -> (exists e h t. Sequence.mem e l /\  h::t = e /\ h = p)) /\ 
            (forall i:int, j:int, ei:C.t list, ej:C.t list, hi:C.t, ti:C.t list, hj:C.t, tj:C.t list.
              0 <= i < List.length l /\
              0 <= j < List.length l /\
              ei = Sequence.get l i /\
              ej = Sequence.get l j /\
              i <> j /\  hi::ti = ei /\  hj::tj = ej ->  hj <> hi)->
              (forall e h t. Sequence.mem e l /\ h::t = e -> Sequence.mem h ps /\ (forall ti. Sequence.mem ti t -> not Sequence.mem ti ps)) ->
                is_epg (ps::l)
              *)
     
    (*@ lemma acyclic_concat_with_list_of_unique_elements_is_acyclic:
          forall l: C.t list list, ps: C.t list.
            (forall e. Sequence.mem e l -> distinct e) /\ (distinct ps) /\ (acyclic_precedence_graph l) /\ (List.length ps = List.length l) /\ 
            (forall p. Sequence.mem p ps -> (exists e h t. Sequence.mem e l /\  h::t = e /\ h = p)) /\ 
            (forall i:int, j:int, ei:C.t list, ej:C.t list, hi:C.t, ti:C.t list, hj:C.t, tj:C.t list.
              0 <= i < List.length l /\
              0 <= j < List.length l /\
              ei = Sequence.get l i /\
              ej = Sequence.get l j /\
              i <> j /\  hi::ti = ei /\  hj::tj = ej ->  hj <> hi)->
              (forall e h t. Sequence.mem e l /\ h::t = e -> Sequence.mem h ps /\ (forall ti. Sequence.mem ti t -> not Sequence.mem ti ps)) ->
                acyclic_precedence_graph (ps::l)
    *)
  
  (* List.for_all *)
  let rec for_all f l =
    match l with
    | [] -> true
    | h::t -> f h && for_all f t
  (*@ r = for_all f l
    ensures r = (forall x. List.mem x l -> f x)
    variant l
  *)

  let rec is_candidate_valid c lins = 
    match lins with
    | [] -> true
    | h::t -> 
      (match h with
      | [] -> true
      | h::t -> C.eq h c || not (List.mem c t)) && (is_candidate_valid c t)  
  (*@ r = is_candidate_valid c lins 
  requires (forall lin. Sequence.mem lin lins -> distinct lin)
  ensures r <-> is_candidate_valid c lins
  variant lins *)

  let rec filter_heads (l: C.t list list) =
    match l with
    | [] -> []
    | (h :: _) :: t -> h :: filter_heads t
    | [] :: t -> filter_heads t
  (*@ r = filter_heads l
    ensures forall y. List.mem y r -> (exists x h t. List.mem x l /\ h::t = x /\ h = y)
    ensures (forall x h t. List.mem x l /\ x = h::t -> List.mem h r)
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
    ensures forall i. 0 <= i < List.length r -> is_removed (Sequence.get l i) (Sequence.get r i) e
    ensures forall i. Sequence.mem i r -> distinct i
    ensures sum_lengths r < sum_lengths l
    ensures List.length r = List.length l
    ensures r <> []
  *)
  
   

  let rec merge (linearizations : C.t list list) : C.t list  =
    if for_all ((fun l -> List.length l = 0)) linearizations then []
    else
      let heads = filter_heads linearizations 
        in 
      let find_candidate (heads: C.t list) =
        
        let rec try_heads (l: C.t list) = match (l: C.t list) with
          | [] -> assert false  
          | candidate :: rest ->
              if is_candidate_valid candidate linearizations then candidate
              else try_heads rest
        (*@ r = try_heads l
        variant l 
        requires forall i. List.mem i l -> (exists j h t. List.mem j linearizations /\ h::t = j /\ h=i )
        requires exists c. Sequence.mem c l /\ is_candidate_valid c linearizations
        ensures (exists j. List.mem j linearizations /\ (has_head j r) ) 
        ensures is_candidate_valid r linearizations
        *)
        in
        try_heads heads
      (*@ r = find_candidate heads
      requires forall i. List.mem i heads -> (exists j h t. List.mem j linearizations /\ h::t = j /\ h=i )
      requires exists c. Sequence.mem c heads /\ is_candidate_valid c linearizations
      ensures is_candidate_valid r linearizations*)
      in
      
      
      let candidate = find_candidate heads in
      let merged = merge (remove linearizations candidate) in
      candidate :: merged
  (*@ l = merge lins
        requires lins <> []
        requires forall i. 0 <= i < List.length lins -> distinct (Sequence.get lins i) 
        requires acyclic_precedence_graph lins

        ensures distinct l
        ensures forall ia ib. 0 <= ia < ib < List.length l ->
          let ea = Sequence.get l ia in
          let eb = Sequence.get l ib in 
          exists ja jb lin.  
            Sequence.mem lin lins /\ Sequence.mem ea lin /\ Sequence.mem eb lin /\ ea = Sequence.get lin ja /\ eb = Sequence.get lin jb /\ ja < jb
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
              
              ensures acyclic_precedence_graph r
              ensures acyclic_precedence_graph (List.append r (ps::[]))
                     
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
