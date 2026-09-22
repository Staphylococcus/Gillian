# Numeric text and runtime constants

Run `GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/number-text-soundness/run.py`.
Controls require the expected exit and diagnostic, including false-postcondition
negatives; crashes and timeouts do not count. Actual ToLength, array-index and
compiled JavaScript formatter/parser bodies are included.

Concrete parser/formatter agreement, signed zeros, noncanonical numeric strings,
integer wrapping/truncation, symbolic formatter roundtrips and fixed runtime
constants use the existing concrete semantics as their reference. Fixed
constants are resolved before reduction can cancel or compare their syntax.
Unmodelled random/time constants are rejected at the total execution boundary.
The GIL lexer accepts the scientific literals and named constants printed by
the syntax layer. Arbitrary symbolic string parsing remains uninterpreted.
