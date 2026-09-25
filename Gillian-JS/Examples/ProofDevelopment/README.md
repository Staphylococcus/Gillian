# Pending exact-count proof

These inputs are not accepted regression cases. `ucs2length-exact.js` retains
the accepted AJV executable AST and original language-string entry. Its recursive
relation now receives the existing numeric length with an explicit equality to
the string length, avoiding the earlier mixed string/numeric bound query.
Automatic inverse witnesses then failed; explicit old-position/count fold
witnesses are checked proof annotations, not assumed results.

The parser now retains the trailing fold. Declaring predecessor witnesses in
`[step: #previous, #previous_count]` prevents an unnecessary inverse-arithmetic
discharge, including a signed-zero mismatch. The original successor relation
is still checked. Four compiled positive/rejection controls exercise that
existing label mechanism; no backend rule is changed.

The numeric advance lemma now lives in the strict regression suite and has
positive, wrong-body, false-lemma and unchecked-consumption controls. This probe
applies it only after it proves in the same run. Select both obligations:

```sh
gillian-js verify ucs2length-exact.js --total --proc=ucs2length --lemma=Ucs2NumericAdvance
```

The latest source-bound probe proves the lemma, then reaches its original
90-second allowance. This is not exact-count acceptance. The helper AST, entry,
invariant, prefix relation and postcondition are unchanged. Rejected search and
annotation attempts are retained in the sibling PoC's
`prefix-search-development.json`; the checked arithmetic and final helper probe
are in `arithmetic-lemma-observations.json`. The next obligation is to align the
proved arithmetic facts with actual next values at folding/backedge, then prove
the complete loop and reject its wrong-count mutants. See the sibling PoC's
`docs/full-proof-roadmap.md`. These inputs remain outside strict acceptance.
