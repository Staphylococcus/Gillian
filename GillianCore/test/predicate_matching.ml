open Gillian.Gil_syntax
module Preds = Engine.Preds
module SI = Utils.Containers.SI

let consume ?(maintain = false) predicates name args ins =
  Preds.consume_pred ~maintain predicates name args (SI.of_list ins) Expr.equal

let expect label expected actual =
  Alcotest.(check bool) label true (expected = actual)

let nullary () =
  let predicates = Preds.init [ ("Context", []); ("Other", []) ] in
  expect "consume the owned nullary predicate" (Some ("Context", []))
    (consume predicates "Context" [] []);
  expect "preserve the unrelated resource" [ ("Other", []) ]
    (Preds.to_list predicates);
  expect "consumed ownership cannot be reused" None
    (consume predicates "Context" [] [])

let output_only () =
  let value = Expr.int 7 in
  let predicates = Preds.init [ ("Witness", [ value ]) ] in
  expect "learn an unknown output with no inputs" (Some ("Witness", [ value ]))
    (consume predicates "Witness" [ None ] []);
  expect "consume the output-bearing resource" [] (Preds.to_list predicates)

let maintain () =
  let predicates = Preds.init [ ("Context", []); ("Context", []) ] in
  expect "maintain returns the existing assertion" (Some ("Context", []))
    (consume ~maintain:true predicates "Context" [] []);
  Alcotest.(check int) "maintain does not remove either copy" 2
    (Preds.length predicates);
  ignore (consume predicates "Context" [] []);
  Alcotest.(check int) "ordinary matching consumes exactly one copy" 1
    (Preds.length predicates)

let missing_and_wrong_input () =
  let predicates = Preds.init [ ("Other", []); ("Owned", [ Expr.int 3 ]) ] in
  let before = Preds.to_list predicates in
  expect "missing name cannot invent ownership" None
    (consume predicates "Context" [] []);
  expect "wrong input cannot match" None
    (consume predicates "Owned" [ Some (Expr.int 4) ] [ 0 ]);
  expect "rejections preserve all resources" before (Preds.to_list predicates)

let reject_inputs_before_outputs () =
  let output = Expr.LVar "#unrelated_output" in
  let predicates = Preds.init [ ("Segment", [ Expr.int 1; output ]) ] in
  let before = Preds.to_list predicates and output_queries = ref 0 in
  let eq left right =
    if Expr.equal left output then incr output_queries;
    Expr.equal left right
  in
  expect "mismatched inputs still reject" None
    (Preds.consume_pred ~maintain:false predicates "Segment"
       [ Some (Expr.int 2); Some (Expr.LVar "#wanted_output") ]
       (SI.singleton 0) eq);
  Alcotest.(check int) "no output query after input rejection" 0 !output_queries;
  expect "input rejection preserves resources" before (Preds.to_list predicates)

let semantic_output_ranking () =
  let input = Expr.int 1 and output = Expr.int 7 in
  let alias = Expr.LVar "#alias" in
  let predicates = Preds.init
      [ ("Segment", [ input; Expr.int 3 ]); ("Segment", [ input; output ]) ] in
  let eq left right = Expr.equal left right ||
    (Expr.equal left output && Expr.equal right alias) in
  expect "matching inputs retain semantic output preference"
    (Some ("Segment", [ input; output ]))
    (Preds.consume_pred ~maintain:false predicates "Segment"
       [ Some input; Some alias ] (SI.singleton 0) eq);
  expect "unselected output resource remains"
    [ ("Segment", [ input; Expr.int 3 ]) ] (Preds.to_list predicates)

let semantic_input_and_output_only () =
  let input = Expr.int 1 and alias = Expr.LVar "#alias" in
  let eq left right = Expr.equal left right ||
    (Expr.equal left input && Expr.equal right alias) in
  let predicates = Preds.init [ ("Input", [ input ]); ("Output", [ input ]) ] in
  expect "semantic input matching is retained" (Some ("Input", [ input ]))
    (Preds.consume_pred ~maintain:false predicates "Input" [ Some alias ]
       (SI.singleton 0) eq);
  expect "known output with no inputs is checked semantically"
    (Some ("Output", [ input ]))
    (Preds.consume_pred ~maintain:false predicates "Output" [ Some alias ]
       SI.empty eq);
  expect "both exclusive resources were consumed" [] (Preds.to_list predicates)

let reject_remaining_inputs () =
  let wrong_object = Expr.ALoc "wrong" and wanted_object = Expr.ALoc "wanted" in
  let wrong_length = Expr.LVar "#unrelated_length" in
  let length_alias = Expr.LVar "#length_alias" and wanted_length = Expr.int 7 in
  let output = Expr.LVar "#output" in
  let wrong = ("Segment", [ wrong_object; wrong_length; output ]) in
  let right = ("Segment", [ wanted_object; wanted_length; output ]) in
  let predicates = Preds.init [ wrong; right ] in
  let unrelated_queries = ref 0 and semantic_queries = ref 0 in
  let eq left right =
    if Expr.equal left wrong_length then (
      incr unrelated_queries;
      failwith "unrelated length must not be queried")
    else if Expr.equal left wanted_length && Expr.equal right length_alias then (
      incr semantic_queries;
      true)
    else Expr.equal left right
  in
  let args = [ Some wanted_object; Some length_alias; None ] in
  expect "select the owned object with a semantic length match" (Some right)
    (Preds.consume_pred ~maintain:false predicates "Segment" args
       (SI.of_list [ 0; 1 ]) eq);
  Alcotest.(check int) "no remaining input query after object mismatch" 0
    !unrelated_queries;
  Alcotest.(check int) "a later input of a viable candidate is checked" 1
    !semantic_queries;
  expect "wrong-object ownership remains" [ wrong ] (Preds.to_list predicates);
  expect "wrong object cannot supply the requested ownership" None
    (Preds.consume_pred ~maintain:false predicates "Segment" args
       (SI.of_list [ 0; 1 ]) eq);
  Alcotest.(check int) "rejection still avoids unrelated length queries" 0
    !unrelated_queries;
  expect "failed consumption preserves ownership" [ wrong ]
    (Preds.to_list predicates)

let insertion_length_dependencies () =
  let module MP = Gillian.Abstraction.MP in
  let keys = Expr.LVar "#keys" and position = Expr.LVar "#position" in
  let key = Expr.LVar "#key" and result = Expr.LVar "#result" in
  let length = Expr.UnOp (LstLen, Expr.NOp (LstInsert, [ keys; position; key ])) in
  let known = Expr.Set.of_list [ keys; position; key ] in
  let equality = Asrt.Pure (Expr.BinOp (result, Equal, length)) in
  let plan known = MP.s_init_atoms ~preds:(Hashtbl.create 0)
      (Expr.Set.add result known) [ equality ] in
  Alcotest.(check bool) "known insertion operands no longer crash planning" true
    (Result.is_ok (plan known));
  List.iter
    (fun operand ->
      Alcotest.(check bool) "every insertion operand is required" false
        (Result.is_ok (plan (Expr.Set.remove operand known))))
    [ keys; position; key ];
  let length_only = Expr.Set.add (Expr.UnOp (LstLen, keys))
      (Expr.Set.remove keys known) in
  Alcotest.(check bool) "list length alone cannot supply the inserted list" false
    (Result.is_ok (plan length_only));
  expect "result length cannot invent insertion witnesses" []
    (MP.learn_expr (Expr.Set.singleton result) result length);
  match plan known with
  | Ok [ (_, outs) ] -> expect "equality invents no insertion outputs" [] outs
  | _ -> Alcotest.fail "expected one complete equality matching step"

let tests =
  List.map (fun (name, test) -> Alcotest.test_case name `Quick test)
    [
      ("reject remaining inputs", reject_remaining_inputs);
      ("reject inputs before outputs", reject_inputs_before_outputs);
      ("semantic output ranking", semantic_output_ranking);
      ("semantic input and output-only matching", semantic_input_and_output_only);
      ("nullary ownership", nullary);
      ("output-only witness", output_only);
      ("maintain and multiplicity", maintain);
      ("missing name and mismatched input", missing_and_wrong_input);
      ("insertion length dependencies", insertion_length_dependencies);
    ]
