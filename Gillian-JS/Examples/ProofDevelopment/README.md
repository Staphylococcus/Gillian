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
run, but full acceptance still requires intended rejection of all four body
mutants and an explicit final case allowance. Accepted case budgets and native
SMT limits have not changed. The five strict `length-zero-sign*`/`cursor-exit*`
controls separately validate the sign facts and their necessary guards.

The four `ucs2length-exact-*` mutants keep the original entry and proof annotations.
They alter only initial count, lone-unit counting, pair counting, or low-surrogate
recognition. Native witnesses confirm each bug; three automatic-mode symbolic
rejections remain unknown/error. An explicit-entry-fold/manual-mode experiment
also reached required unknown and was discarded. Do not count these as accepted
negative controls. Preserve raw diagnostic bytes: lone surrogates may render as
non-UTF-8 output.

Source-bound reports live in the sibling PoC's `experiments/gillian/symbolic-utf16/`:
`cursor-exit-observations.json`, `canonical-arithmetic-development.json`, and
`cursor-exit-development.json`. The next bounded work is P07.1a2h in its
`docs/full-proof-roadmap.md`; original-schema AJV composition follows acceptance.
