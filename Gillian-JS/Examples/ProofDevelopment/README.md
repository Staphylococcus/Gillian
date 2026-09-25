# Exact-count mutation development

The canonical positive helper and its prefix relation are now in
`../../regressions/js-utf16-values/ucs2length-exact.js` and `Ucs2Prefix.gil`.
The strict total case selects `Ucs2NumericAdvance` in the same run and has an
explicit 180-second watchdog, following the successful 106-second diagnostic.
Final acceptance evidence belongs to the sibling PoC's P07.1a2i checkpoint.

These four symbolic mutant probes remain outside strict acceptance. They keep
the original entry and annotations, changing only initial count, lone-unit
counting, pair counting or low-surrogate recognition. Their unrestricted
symbolic searches include unknown/error results; do not relabel those runs.

The strict `concrete-execution/ucs2length-*` controls already establish every
bug by executing a valid input through compiled JavaScript, with the unchanged
helper on the same inputs as a positive control. The PoC's native replay binds
both body and oracle ASTs to the pinned AJV bundle. These are counterexamples,
not bounded substitutes for the original-domain total proof. Raw diagnostic
bytes are retained because lone surrogates can render as non-UTF-8 output.

Source-bound reports and next steps are in the sibling PoC's
`experiments/gillian/symbolic-utf16/` and `docs/full-proof-roadmap.md`.
