# Exact integer list-length procedure ranks

Accepted frontend regression: the source-bound build, nine parser/printer/lowering
unit cases and all six native controls passed independent receipt review.
The symbolic-list positive succeeds; false postcondition, non-decreasing call,
constant rank, missing rank and nonformal rank controls reject as intended.

`variant(l-len-int xs)` is a procedure-only annotation lowering directly to GIL's
integer `LstLen`, with a single formal parameter operand. Ordinary JSIL `l-len`
retains Number semantics. Existing definedness, integer nonnegativity and strict
descent checks remain authoritative. No engine, runtime or solver change is used.

The positive procedure recurses over the tail of an arbitrary symbolic List,
without a length bound, and returns true. This heap-free frontend regression
does not establish descriptor ownership or the AJV enumeration helper theorem.

The other controls require a genuine false-postcondition rejection, rejection
of an unchanged recursive argument and of a constant rank, plus pre-proof
rejection of missing ranks and nonformal rank operands. A dropped rank cannot
pass the positive; a no-op checker cannot pass the negative controls.

Run `python3 -I -B run.py --out <fresh-directory>` with `GILLIAN_JS` and
`GILLIAN_RUNTIME` set. It imports each fixture through ordinary JavaScript
verification (`--total --proc=drain`, without `-a`), preserves primitive receipts
before classification, streams verbose logs, and stops at the first unexpected
result. Timeout, unknown, crash and unsupported outcomes cannot prove the positive.
All full-proof acceptance flags remain false.
