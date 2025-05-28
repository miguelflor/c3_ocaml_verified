open C3

(* Compute linearization for a given parent map and class *)
let compute_linearization parent_map cls =
  let module CustomClass = struct
    type t = string
    let eq = String.equal
    let getParents c =
      try List.assoc c parent_map with Not_found -> []
    let to_string s = s
  end in
  let module MRO = Make(CustomClass) in
  MRO.c3_linearization cls

(* Define types for tests *)
type test_result =
  | ExpectSuccess of string list
  | ExpectFail

type test = {
  description : string;
  parent_map : (string * string list) list;
  test_class  : string;
  expected    : test_result;
}

(* Define test cases *)
let tests = [
  {
    description = "Test 1: Simple (A -> B -> C)";
    parent_map = [("C", []); ("B", ["C"]); ("A", ["B"])];
    test_class = "A";
    expected = ExpectSuccess ["A"; "B"; "C"];
  };
  {
    description = "Test 2: Diamond";
    parent_map = [("O", []); ("B", ["O"]); ("C", ["O"]); ("A", ["B"; "C"])];
    test_class = "A";
    expected = ExpectSuccess ["A"; "B"; "C"; "O"];
  };
  {
    description = "Test 3: Singleton";
    parent_map = [("A", [])];
    test_class = "A";
    expected = ExpectSuccess ["A"];
  };
  {
    description = "Test 4: Propertie 3";
    parent_map = [("O", []); ("B", ["D";"O"]); ("C", ["O"]); ("A", ["B"; "C"])];
    test_class = "A";
    expected = ExpectSuccess ["A"; "B"; "D" ; "C"; "O"];
  };
  {
    description = "Test 5: Wikipedia";
    parent_map = [
      ("O", []);                
      ("A", ["O"]);             
      ("B", ["O"]);             
      ("C", ["O"]);             
      ("D", ["O"]);             
      ("E", ["O"]);             
      ("K1", ["C";"A";"B"]);  
      ("K2", ["B"; "D"; "E"]);  
      ("K3", ["A";"D"]);       
      ("Z", ["K1"; "K3"; "K2"]) 
    ];
    test_class = "Z";
    expected = ExpectSuccess ["Z"; "K1"; "C"; "K3"; "A"; "K2"; "B"; "D"; "E"; "O"];
  };
  {
    description = "Test 6: Simple test Article";
    parent_map = [
      ("C", ["A";"B"]);
      ("A",[]);
      ("B",[])
    ];
    test_class = "C";
    expected = ExpectSuccess ["C";"A";"B"]
  };
  {
    description = "Test 7: Example 1 Article";
    parent_map = [
      ("E", ["D";"C"]);
      ("D", ["B";"A"]);
      ("A",[]);
      ("B",[]);
      ("C",[])
    ];
    test_class = "E";
    expected = ExpectSuccess ["E";"D";"B";"A";"C"]
  };
  {
    description = "Test 8: Fail case Apresentation";
    parent_map = [
      ("E", ["C";"D"]);
      ("C", ["A";"B"]);
      ("D", ["B";"A"]);
      ("B", []);
      ("A", [])
    ];
    test_class = "E";
    expected = ExpectFail
  };
  {
    description = "Test 9: Fail case article";
    parent_map = [
      ("F", ["E1";"E2";"E3"]);
      ("E1", ["D1";"C"]);
      ("E2", ["B";"D2"]);
      ("E3", ["A";"D3"]);
      ("D1", ["A";"B"]);
      ("D2", ["A";"C"]);
      ("D3", ["B";"C"])
    ];
    test_class = "F";
    expected = ExpectFail
  }
]

let run_tests () =
  List.iter (fun test ->
    match test.expected with
    | ExpectSuccess expected_list ->
        begin
          try
            let result = compute_linearization test.parent_map test.test_class in
            if result = expected_list then
              Printf.printf "%s: passed\n" test.description
            else begin
              Printf.printf "%s: FAILED\n" test.description;
              Printf.printf "  Expected: %s\n  Got: %s\n"
                (String.concat " " expected_list)
                (String.concat " " result);
              exit 1
            end
          with
          | Failure msg ->
              Printf.printf "%s: FAILED (unexpected Failwith: %s)\n" test.description msg;
              exit 1
        end
    | ExpectFail ->
        begin
          try
            let result = compute_linearization test.parent_map test.test_class in
            Printf.printf "%s: FAILED (expected Failwith but got success with the list %s)\n"
             test.description
             (String.concat " " result);
            exit 1
          with
          | Failure _ ->
              Printf.printf "%s: passed (raised Failwith as expected)\n" test.description
          | e ->
              Printf.printf "%s: FAILED (unexpected exception: %s)\n"
                test.description (Printexc.to_string e);
              exit 1
        end
  ) tests

let () =
  run_tests ();
  print_endline "All tests passed!"
