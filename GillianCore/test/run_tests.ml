let test_suites : unit Alcotest.test list =
  [
    ("Gil_syntax.Reducers", Gil_syntax_tests.Visitors.tests);
    ("Binary64", Numeric.tests);
    ("Literal equality", Literal_equality.tests);
    ("Boolean integer", Boolean_integer.tests);
    ("Closed entry", Closed_entry.tests);
    ("Strings", Strings.tests);
    ("UTF-16 bridge", Utf16_bridge.tests);
    ("UTF-16 values", Utf16_values.tests);
    ("Sufficient entailment", Entailment.tests);
  ]

let () = Alcotest.run "Gillian" test_suites
