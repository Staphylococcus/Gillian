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

let tests =
  List.map (fun (name, test) -> Alcotest.test_case name `Quick test)
    [
      ("reject inputs before outputs", reject_inputs_before_outputs);
      ("semantic output ranking", semantic_output_ranking);
      ("semantic input and output-only matching", semantic_input_and_output_only);
      ("nullary ownership", nullary);
      ("output-only witness", output_only);
      ("maintain and multiplicity", maintain);
      ("missing name and mismatched input", missing_and_wrong_input);
    ]
