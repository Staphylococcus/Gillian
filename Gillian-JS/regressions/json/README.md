# JSON execution acceptance

Run from the repository root after installing dependencies and building:

```sh
node Gillian-JS/regressions/json/native.mjs
GILLIAN_JS="dune exec --root $PWD -- gillian-js" \
  python3 Gillian-JS/regressions/json/run.py
```

The runner concatenates the separately hashed JSON model with each control,
uses the full initializer, retains every path and checks cutoff diagnostics.
A backend crash or unrelated assertion failure cannot satisfy the negative
copy control. Timeouts and unsupported symbolic strings never become proofs.

The controls cover nested round trips and fresh references; escaping, astral
characters and lone surrogates; special keys and duplicate keys; syntax errors,
cycles and getter exceptions; replacer/reviver behavior; numeric formatting and
round trips at binary64 boundaries; two symbolic branches selecting finite
concrete trees; a false alias assertion; unsupported unbounded symbolic strings;
and zero exploration budget.

The model and native JSON execute the same test bodies in Node. Additional
seeded finite-tree differential checks compare exact serialized bytes and
parsed values. See `observations.json` for the final local candidate identity
and results, and `../../runtime/JSON/README.md` for scope and provenance.
