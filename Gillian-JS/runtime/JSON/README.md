# JSON execution model

`json3.js` is an explicit ES5 JavaScript implementation of JSON, executed by
Gillian alongside the program being checked. It is not a graph interpreter or a
replacement for a fold's clone helper. It implements the parse/stringify calls
that the existing initializer advertises but does not supply.

The implementation is derived from the MIT-licensed [JSON3 v3.2.6 source](https://github.com/bestiejs/json3/blob/7b89fd94939f970f316420e157a836cc68aa2207/lib/json3.js).
This version has a recursive-descent parser and a character-loop serializer;
it does not need Gillian's unsupported regexp literals or native JSON. The
adjacent LICENSE retains the upstream notice.

Adaptations to that source are deliberately visible in this model:

- Remove module detection, native-JSON delegation, legacy browser probes and
  Date compatibility shims. Use the runtime's ordinary intrinsics and `toJSON`.
- Use `Object.keys` for enumeration and preserve replacer-list order.
- Define parsed/revived properties as own data properties, including `__proto__`;
  visit array reviver entries in ascending order with string keys.
- Propagate getters' exceptions, use the correct primitive coercions and escape
  lone surrogates for well-formed JSON.stringify. Four-digit escaping uses a
  fixed hexadecimal digit table; general radix formatting is not a prerequisite.
- Normalize source string-literal spelling with the PoC's pinned Babel generator
  so Gillian's assertion pre-parser can read it. No program code is transformed
  by this step.

The acceptance scope is ordinary finite JSON trees under the standard,
unmodified intrinsics. The native controls additionally exercise replacer,
reviver, cyclic inputs, getters and toJSON; these are not a general conformance
certificate. Objects that monkey-patch intrinsics, modern exotic objects,
symbols/BigInt and resource-exhaustion behavior are outside this profile.
Gillian has an ES5 frontend. Unsupported symbolic strings remain backend
limitations and cannot be caught as JavaScript exceptions.

Load this model before the program with the full `Init.jsil` initializer, which
supplies `Object.defineProperty`, `Array.prototype.join` and other used
intrinsics. The regression runner does this explicitly. There is currently no
automatic installation into the default initializer, and no claim that its
missing `JSON_parse`/`JSON_stringify` procedures have become native GIL functions.
The source-built PoC candidate runner records this model as a separate hashed
backend component; the lowered classifier remains unchanged.

## Prerequisite repairs

JavaScript strings are normalized to WTF-8 per UTF-16 code unit. JS runtime
length/index/slice/substring and character conversion use that representation;
`eval`/`Function` convert paired code units back to scalar UTF-8 for the parser.
Raw lone surrogates in generated source remain a Flow frontend limitation and
raise backend Unsupported before parsing; they must not become catchable JS
SyntaxErrors. Ordinary JSON strings retain lone surrogates. Procedure names and
call targets use the same canonical encoding, including astral identifiers.
Generic GIL strings and logical `s-len`/`s-nth` retain their existing byte meaning;
this work does not establish Unicode deductive specifications.

Number formatting reuses [Flow's dtoa 0.3.3](https://github.com/flow/ocaml-dtoa/tree/v0.3.3)
`ecma_string_of_float`, replacing the previous lossy hand-written formatter.
The opam dependency is pinned. General nondecimal Number.toString remains a
separate gap and is not used by this JSON model.

Object heaps preserve property creation order across writes, deletion/recreation,
concrete/symbolic value transitions and heap serialization. Enumeration sorts
array-index names first and preserves creation order for other names. Unknown
symbolic keys or conflicting orders after heap merges are explicitly unsupported.
This is execution support, not an order-aware separation-logic specification.

The parser's malformed-input control also found an exception-edge compiler bug:
`for` initializer bookkeeping included a GetValue edge even when that operation
was optimized out. The repair uses the actual emitted edge list. The independent
`loop-exception.js` regression checks throws inside and after such a loop.

## Validation

See `Gillian-JS/regressions/json` for native/backend controls and evidence.
Passing bounded runs does not prove termination or contracts over arbitrary
string lengths, array sizes or recursive JSON depths.
