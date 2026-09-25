module V = Gillian.Utils.Config.Verification

exception Expected

let phase_scope () =
  let saved = !V.closed_entry_heap_abstracted in
  Fun.protect
    ~finally:(fun () -> V.closed_entry_heap_abstracted := saved)
    (fun () ->
      List.iter
        (fun previous ->
          V.closed_entry_heap_abstracted := previous;
          let check label expected =
            Alcotest.(check bool) label expected !V.closed_entry_heap_abstracted
          in
          let execute () =
            check "new invocation starts before abstraction" false;
            V.closed_entry_heap_abstracted := true;
            check "abstraction persists within invocation" true
          in
          V.with_fresh_closed_entry_heap_phase execute;
          check "success restores the previous scope" previous;
          Alcotest.check_raises "exception escapes after restoring scope"
            Expected (fun () ->
              V.with_fresh_closed_entry_heap_phase (fun () ->
                  execute ();
                  raise Expected));
          check "exception restores the previous scope" previous;
          V.with_fresh_closed_entry_heap_phase (fun () ->
              check "next invocation also starts before abstraction" false);
          check "next invocation restores its caller" previous)
        [ false; true ])

let tests = [ Alcotest.test_case "heap phase scope" `Quick phase_scope ]
