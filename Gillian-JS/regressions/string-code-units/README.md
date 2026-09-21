# First JSON prerequisite: character codes and literal values

This slice adds `String.prototype.charCodeAt` to the normal JS runtime, with
registration in both normal initializers. It follows the coercion order and
UTF-16 indexing of [ES5.1 section 15.5.4.5](https://262.ecma-international.org/5.1/#sec-15.5.4.5).

The implementation uses the existing Flow dependency `wtf8` to decode concrete
strings. Astral characters produce two code units; lone surrogates are retained.
Malformed internal encodings stop analysis rather than becoming replacement
characters. Coercion, bounds checks and indexing execute in `String.jsil`; the
small external operation only decodes the string into a GIL list.

The quote control also exposed an existing compiler defect: a quote was stored
as a backslash followed by a quote. Literal values now remain unchanged in the
compiler. Escaping happens only when printing GIL, with print/parse round-trip
tests. The compensating unescaping in `eval` and `Function` has been removed;
both have native and Gillian controls for generated quoted code.

## Validation

```sh
dune build -p gillian,gillian-js
dune runtest GillianCore Gillian-JS/JS_Parser/test Gillian-JS/test
node Gillian-JS/regressions/string-code-units/native.mjs
GILLIAN_JS="dune exec --root $PWD -- gillian-js" \
  python3 Gillian-JS/regressions/string-code-units/run.py
GILLIAN_JS="dune exec --root $PWD -- gillian-js" \
  python3 Gillian-JS/regressions/numeric-soundness/run.py
```

Rebuild the installed runtime with `dune build -p` after editing `.jsil` files;
building the executable alone can leave its runtime copy stale. Each regression
uses normal logging with heap dumps disabled and checks for exploration cutoffs.
Set `GILLIAN_RESULTS_ROOT` to retain character-code logs outside a temporary
container. Node checks the same JS bodies, with only the analysis directive
removed and symbolic Boolean choices enumerated.

Controls cover BMP characters, astral pairs, both lone-surrogate ranges, quotes,
backslashes, control characters, bounds, fractional and non-finite positions,
receiver/index coercion order and exceptions, string property keys, and generated
code. The UTF-16 unit suite exercises all 65,536 individual code units and malformed
encodings. Negative controls reject a code-point result in place of a code unit,
and distinguish unsupported execution and exhausted exploration from success.

[observations.json](observations.json) records the locally built source/binary
identities and passing controls: eight character-code/literal controls, eight
existing numeric controls, all eight unchanged lowered-Boolean/AJV controls and
the character-code checks under the full initializer. The literal-value control
fails at its assertion on the prior pinned image and passes with this patch.
The native suite checks 36 assertions; the OCaml suites pass 11 core, 70 parser
and two UTF-16 tests (including the complete single-code-unit matrix).

## Subsequent local slices

The current suite additionally covers UTF-16 length/index/charAt/slice/substring,
canonical equality and concatenation, `String.fromCharCode`, trim, property
creation order and the for-initializer exception-edge regression. It now has
13 backend controls and 70 native assertions. UTF-16 units also test canonical
encoding and concatenation; property-order units check partition/union, deletion,
serialization and concrete/symbolic transitions.

The historical `observations.json` above describes only the first slice. Current
combined evidence is in `../json/observations.json`, with model scope and
remaining limitations in `../../runtime/JSON/README.md`.

The separate bi-abduction runtime is unchanged. Unbounded symbolic strings,
order-aware deductive specifications, recursive JSON invariants and full-contract
termination remain open. General nondecimal Number.toString remains unchanged
by this work; the JSON implementation does not use it.
