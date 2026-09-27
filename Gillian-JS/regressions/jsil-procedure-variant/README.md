# Imported JSIL procedure variants

Checked frontend extension (27 September 2026). A JSIL specification
case may put `variant(expression)` after its postconditions and before `normal`
or `error`. Omitting it keeps the previous behavior. Parsing, printing and GIL
lowering preserve the measure, including JS numeric conversion of list lengths.
Procedure measures must have GIL integer type. The fixtures therefore use
`variant(as_int n)` with a checked finite, integral, nonnegative JS-number
precondition. A bare `variant(n)` remains numeric and is correctly rejected by
the existing procedure-entry guard. No implicit rank coercion is introduced.
Existing totality checks still enforce entry naturalness, strict recursive
descent, formal-parameter scope and agreement across specification cases.

`entry.js` imports the selected fixture as `Ranked.jsil`. The runner uses the
ordinary JavaScript verifier path, selecting the imported `count` procedure.
Its bounded numeric input is a frontend regression, not an enumeration theorem.

Run `python3 -B run.py --out <fresh-directory>` with `GILLIAN_JS` set to the
verifier command and, when needed, `GILLIAN_RUNTIME` to the installed runtime.
The five sequential controls require a successful decreasing recursion, a
genuine wrong-postcondition failure, two strict-descent failures (unchanged
argument and constant rank), and the existing missing-rank rejection. Stop on
the first unexpected result. Primitive statuses and raw logs precede assessment;
timeouts, parsing failures and terminal SMT unknown never pass.

The Alcotest `jsil_variant_tests.exe` separately checks normal/error roundtrips,
legacy defaults, multiple cases, list-length lowering and malformed syntax.
No runtime helper is trusted or changed. Full finite-JSON admission, actual
enumeration helper proofs and final adapters remain open.

Validation: pinned-image build, 6/6 parser/lowering units, and all five imported
native controls passed on binary `b79d497d`. The earlier bare-number measure
was rejected at entry, confirming the integer-type requirement. Source-bound
receipts and limits are recorded in `observations.json`. These results accept
the frontend feature; they do not establish an enumeration helper theorem.
