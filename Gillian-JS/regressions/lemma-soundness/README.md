# Lemma-checking soundness controls

The verifier distinguishes no possible conclusion from one empty conclusion.
Previously, postcondition normalization could remove every alternative and
`MP.build_mp []` would return an immediately successful match. The matching plan
now consumes `false` in that case. A surviving `emp` alternative still succeeds.

Self-recursive lemmas now require a checked natural integer variant:

- The expression depends only on formal parameters (`n` or `#n`). Its normalized
  entry value must be an integer at least zero; its logical variables are kept
  through simplification.
- Before each self-application, the actual arguments must give a nonnegative
  integer measure strictly below that entry value. The conclusion cannot supply
  the evidence for its own decrease.
- Nonrecursive macro wrappers receive the same checks. Mutual lemma recursion,
  missing/non-parameter measures and macro-only cycles remain unsupported.
- Selected lemmas are checked in dependency order. Every normalized proof case
  must pass before a recursive summary is available to a caller. Selecting only
  the caller rejects the omitted proof. Unused recursive lemmas do not block an
  independent selected procedure.

A GIL example uses mathematical integers rather than JavaScript Numbers:

```text
pure nounfold pred Counted(n : Int) :
  (n == 0i), (0i i< n) * Counted(n i- 1i);
lemma Count(n) variant(#n)
[[ types(#n : Int) * (0i i<= #n) ]]
[[ Counted(#n) ]]
[* if (#n i> 0i) then { apply Count(#n i- 1i) }; fold Counted(#n) *]
```

The proof covers every nonnegative integer. Removing its induction hypothesis
fails. The list control similarly proves `Counted(l-len #xs)` for arbitrary
finite lists. JSIL currently translates `l-len` to a Number, so a bridge from
JavaScript sizes to logical integers is still separate work.

Run against a built executable with its matching runtime:

```sh
GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/lemma-soundness/run.py
```

`GILLIAN_JS` accepts a command or wrapper that adds the appropriate runtime path.
`GILLIAN_RESULTS_ROOT` optionally selects the parent output directory. Each result
records its source hash, command, output and expected exit/message. A crash,
timeout or unrelated rejection does not satisfy a negative control.

The 43 controls include valid nonrecursive and inductive proofs, false conclusions
before/after substitution, absent/increasing/constant/negative/non-integer ranks,
false base cases, macros and caller selection. One split-precondition control has
one passing proof case and one failing base case; its caller must not get the
summary. Multiple recursive calls compare against the same captured entry value.

This is a lemma induction rule, not program total-correctness certification.
Axiomatic lemmas and unselected acyclic summaries retain their existing assumption
semantics; automatic proof-dependency discharge remains pending. The infinite-loop
and non-progressing function-recursion controls still pass in ordinary `verify`
mode, which establishes partial correctness only.

`observations.json` preserves the earlier conservative repair's 19-control report
on executable `d4948bdf293ae2208fb2bd60aa0569bed585a12b52b13e941df957f2f4cf45e8`.
`induction-observations.json` records 43/43 controls on executable
`61cd21b2f1401f3f85424a645ada23fd7cea572150321b44ca38213132454a92`, with changed
backend source/fixture hashes, eight numeric regressions and sixteen unit tests.
