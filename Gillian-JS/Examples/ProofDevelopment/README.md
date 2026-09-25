# Pending exact-count proof

These are development inputs, not accepted regression cases. `ucs2length-exact.js`
retains the accepted AJV executable body and original language-string entry,
adding the proposed recursive relation from `Ucs2Prefix.gil` to its invariant
and postcondition. No lemma or result is assumed. Earlier diagnostics reached the pair-step position bound and returned native SMT
unknown; the latest reached the same query and hit its 90-second case cap. Both
remain non-proofs.

The source-bound diagnostic and next steps are retained by the sibling PoC at
`experiments/gillian/symbolic-utf16/prefix-development.json` and
`docs/full-proof-roadmap.md`. Exact count and its rejection controls must pass
before these become accepted regression fixtures. Keep the strict regression
catalogue complete; do not add pending programs to its support allowlist.
