# Exact-count proof development

These files remain outside the strict acceptance catalogue. The actual AJV
helper keeps its original executable AST and language-string entry. Its exact
prefix relation, resource postcondition and decreasing loop rank are unchanged.

The invariant now proves that cursor and length are not negative zero. At exit,
a checked value-equality assertion permits direct reuse of the prefix predicate.
A checked count-increment assertion keeps the arithmetic lemma and fold aligned.
The arithmetic lemma must prove in the same run before its result is applied:

```sh
gillian-js verify ucs2length-exact.js --total --proc=ucs2length --lemma=Ucs2NumericAdvance
```

This candidate passed total verification in 106.32 seconds under a separately
recorded 300-second diagnostic watchdog. That is a successful exact-post proof
run, but full acceptance still requires strict theorem registration and final
validation alongside the now-validated compiled counterexamples. Accepted case budgets and native
SMT limits have not changed. The five strict `length-zero-sign*`/`cursor-exit*`
controls separately validate the sign facts and their necessary guards.

The four `ucs2length-exact-*` mutants keep the original entry and proof annotations.
They alter only initial count, lone-unit counting, pair counting, or low-surrogate
recognition. Their unrestricted symbolic runs still include unknown/error results.
Separate strict concrete-execution controls now establish every bug by replaying
a valid input through actual compiled JavaScript, with the original helper as a
positive control. The PoC native replay binds both body and checking harness ASTs
to the pinned bundle. These are counterexamples, not bounded positive proofs.
An explicit-entry-fold/manual-mode proof attempt was discarded. Raw diagnostic
bytes are retained because lone surrogates can render as non-UTF-8 output.

Source-bound reports live in the sibling PoC's `experiments/gillian/symbolic-utf16/`:
`cursor-exit-observations.json`, `canonical-arithmetic-development.json`, and
`cursor-exit-development.json`. The next bounded work is P07.1a2i in its
`docs/full-proof-roadmap.md`; strict exact-theorem registration comes next, then original-schema AJV composition.
