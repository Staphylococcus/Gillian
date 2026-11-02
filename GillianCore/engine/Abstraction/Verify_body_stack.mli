(** Optional passive BODY diagnostics, configured once from
    GILLIAN_VERIFY_BODY_STACK_DIR and GILLIAN_VERIFY_BODY_STACK_TARGET.
    With both absent, this is a direct call and signal handlers are untouched.
    Selected bodies emit their original (public, normalized) test identity.
    At most two SIGUSR1 snapshots contain up to 128 current OCaml frames.
    Output is exclusive/private, at most 64KiB per file and 1MiB per process.
    A configured handler remains a no-op outside a selected active BODY,
    including after capture failure/caps. Diagnostic errors disable capture.
    The action's value, exception object and raw exception backtrace are retained. *)
val with_body : target:string -> case_id:(int * int) -> (unit -> 'a) -> 'a
