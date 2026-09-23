let test_suites : unit Alcotest.test list =
  [
    ("Gil_syntax.Reducers", Gil_syntax_tests.Visitors.tests);
    ("Binary64", Numeric.tests);
    ("Strings", Strings.tests);
    ("UTF-16 bridge", Utf16_bridge.tests);
    ("UTF-16 values", Utf16_values.tests);
  ]

let () = Alcotest.run "Gillian" test_suites
