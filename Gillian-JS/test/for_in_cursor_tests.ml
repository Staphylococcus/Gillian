open Jsil_syntax
open LabCmd

module Compiler = Js2jsil_lib.JS2JSIL_Compiler

let compile ?(total = false) source =
  let previous_mode = !Gillian.Utils.Config.current_exec_mode in
  let previous_total = !Gillian.Utils.Config.Verification.total in
  Fun.protect
    ~finally:(fun () ->
      Gillian.Utils.Config.current_exec_mode := previous_mode;
      Gillian.Utils.Config.Verification.total := previous_total)
    (fun () ->
      Hashtbl.clear Compiler.cc_tbl;
      Hashtbl.clear Compiler.fun_tbl;
      Hashtbl.clear Compiler.old_fun_tbl;
      Hashtbl.clear Compiler.vis_tbl;
      Js2jsil_lib.JS2JSIL_Helpers.reset_generators ();
      Gillian.Utils.Config.current_exec_mode := Verification;
      Gillian.Utils.Config.Verification.total := total;
      let ast = JS_Parser.parse_string_exn source in
      let program, _, _ = Compiler.js2jsil ~filename:"cursor.js" ast true in
      (Option.get (EProg.get_proc program "main")).body |> Array.to_list)

let cursor_phis commands =
  let fields =
    List.filter_map
      (function _, _, LBasic (BCmd.GetFields (keys, _)) -> Some keys | _ -> None)
      commands
  in
  List.concat_map
    (function
      | _, _, LPhiAssignment pairs ->
          List.filter_map
            (function
              | current, [ Expr.PVar first; Expr.PVar next ]
                when List.mem first fields ->
                  Some (current, next)
              | _ -> None)
            pairs
      | _ -> [])
    commands

let assert_cursor commands (current, next) =
  let has command = List.exists (fun (_, _, c) -> c = command) commands in
  Alcotest.(check bool)
    "backedge consumes the carried List" true
    (has (LBasic (BCmd.Assignment (next, Expr.UnOp (Cdr, PVar current)))));
  Alcotest.(check bool)
    "empty List terminates before reading its head" true
    (List.exists
       (function
         | _, _, LGuardedGoto
             (UnOp (Not, BinOp (PVar p, Equal, EList [])), _, _)
           when p = current -> true
         | _ -> false)
       commands);
  Alcotest.(check bool)
    "key comes from the remaining List" true
    (List.exists
       (function
         | _, _, LBasic (BCmd.Assignment (_, UnOp (Car, PVar p))) -> p = current
         | _ -> false)
       commands)

let list_cursor () =
  let commands = compile "'use strict'; var k; for (k in {z: 1, a: 2}) {}" in
  let cursors = cursor_phis commands in
  Alcotest.(check int) "one enumeration cursor" 1 (List.length cursors);
  List.iter (assert_cursor commands) cursors;
  Alcotest.(check bool)
    "enumeration has no Number length, comparison or increment" false
    (List.exists
       (function
         | _, _, LBasic (BCmd.Assignment (_, UnOp (LstLen, _)))
         | _, _, LBasic (BCmd.Assignment (_, BinOp (_, FPlus, _)))
         | _, _, LGuardedGoto (BinOp (_, FLessThan, _), _, _) -> true
         | _ -> false)
       commands)

let nested_jumps () =
  let commands =
    compile
      "'use strict'; var k, j; outer: for (k in {z: 1}) { for (j in {a: 2}) \
       { if (j === 'a') continue outer; break outer; } }"
  in
  let cursors = cursor_phis commands in
  Alcotest.(check int) "independent nested cursors" 2 (List.length cursors);
  List.iter (assert_cursor commands) cursors

let header_invariant () =
  let commands =
    compile ~total:true
      "'use strict'; var k; /* @invariant (False) variant(0) */ for (k in {}) {}"
  in
  let rec at_header = function
    | (_, Some _, LPhiAssignment _)
      :: (_, None, LLogic (LCmd.SL (Jsil_syntax.SLCmd.Invariant _)))
      :: _ -> true
    | _ :: rest -> at_header rest
    | [] -> false
  in
  Alcotest.(check bool)
    "total invariant follows the cursor PHI" true (at_header commands);
  List.iter (assert_cursor commands) (cursor_phis commands)

let visible_number_counter () =
  let commands = compile "'use strict'; var n; for (n = 0; n < 3; n++) {}" in
  Alcotest.(check int) "ordinary for has no enumeration cursor" 0
    (List.length (cursor_phis commands));
  Alcotest.(check bool)
    "visible increment remains binary64 addition" true
    (List.exists
       (function
         | _, _, LBasic (BCmd.Assignment (_, BinOp (_, FPlus, _))) -> true
         | _ -> false)
       commands)

let () =
  Alcotest.run "For-in enumeration cursors"
    [
      ( "compiler",
        [
          Alcotest.test_case "List cursor without numeric limit" `Quick list_cursor;
          Alcotest.test_case "nested continue and break" `Quick nested_jumps;
          Alcotest.test_case "ranked header placement" `Quick header_invariant;
          Alcotest.test_case "ordinary Number counter" `Quick visible_number_counter;
        ] );
    ]
