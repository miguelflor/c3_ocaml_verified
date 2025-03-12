
type class_name = string

type class_hierarchy = (class_name * class_name list) list

let rec assoc_opt (key: class_name) (lst: class_hierarchy) =
  match lst with
  | [] -> None
  | (k, v) :: rest -> if (String.compare key k) = 0 then Some v else assoc_opt key rest

let filter_map f lst =
  List.fold_right (fun x acc ->
    match f x with
    | Some v -> v :: acc
    | None -> acc
  ) lst []

let rec for_all predicate lst =
  match lst with
  | [] -> true  
  | x :: xs -> if predicate x then for_all predicate xs else false
  
let get_parents (hierarchy: class_hierarchy) (class_name: class_name) : class_name list =
  match assoc_opt class_name hierarchy with
  | Some parents -> parents
  | None -> []

let rec list_mem (x: class_name) (l: class_name list) : bool =
  match l with
  | [] -> false
  | h :: t -> (String.compare h x) = 0 || list_mem x t

let rec list_remove (x: class_name) (l: class_name list) : class_name list =
  match l with
  | [] -> []
  | h :: t -> if (String.compare h x) = 0 then t else h :: list_remove x t

let rec merge (linearizations: class_name list list) : class_name list =
  let all_empty = for_all (fun l -> List.length l = 0 ) linearizations in
  if all_empty then []
  else
    let get_head l = match l with [] -> None | h :: _ -> Some h in
    let heads = filter_map get_head linearizations in
    
    let rec find_valid_candidate candidates =
      match candidates with
      | [] -> None
      | candidate :: rest ->
          let is_valid = List.for_all 
            (fun l -> 
              match l with
              | [] -> true
              | h :: t -> h = candidate || not (list_mem candidate t))
            linearizations in
            
          if is_valid then Some candidate
          else find_valid_candidate rest
    in
    
    match find_valid_candidate heads with
    | None -> failwith "Cannot create a consistent linearization"
    | Some candidate ->
        let updated_linearizations = List.map
          (fun l -> 
            match l with
            | [] -> []
            | h :: t -> if h = candidate then t else h :: t)
          linearizations in
          
        candidate :: merge updated_linearizations

let rec c3_linearization (hierarchy: class_hierarchy) (class_name: class_name) : class_name list =
  let parents = get_parents hierarchy class_name in
  
  let parent_linearizations = List.map (c3_linearization hierarchy) parents in
  
  let linearizations = parent_linearizations @ [parents] in
  
  class_name :: merge linearizations

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
  
  let result = c3_linearization hierarchy "Z" in
  result