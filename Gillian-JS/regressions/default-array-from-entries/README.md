# Selected default-array Object.fromEntries MODEL

This is the conditional N2 capability candidate, not arbitrary iterable support.
The original normalizer and public finite-JSON target are unchanged.

Its caller supplies a fresh ordinary mapped array and fresh data-only pairs,
primitive string keys and the unchanged captured default array iteration
protocol. N2 needs exactly two entries: payload (the arbitrary admitted copied
payload reference) and statusCode (200), in either order. Existing input, entries,
pairs, frame, activation/Trace, Set tombstones and Map entries remain owned.

The simulation maps the default iterator's position/done state to local
index/length and hides only fresh nonescaping iterator and IteratorResult
allocations. Each iteration reads current length, actual entry, key/value and
produces a fresh ordinary target's configurable/writable/enumerable data cell.
No custom iterator, accessor, next/return override, prototype mutation or private
identity observation is admitted. This is observational correspondence under a
selected MODEL, not identical concrete residual heaps or public MODEL closure.
It does not permit discarding an existing modeled resource.

Specification: [Object.fromEntries](https://tc39.es/ecma262/multipage/fundamental-objects.html#sec-object.fromentries),
[AddEntriesFromIterable](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-add-entries-from-iterable),
[CreateArrayIterator](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-createarrayiterator).
The data-only, primitive-key path invokes no user code. A fresh extensible ordinary
target and its own configurable data fields justify direct CreateDataProperty
cell production, including overwrites. Length is reread on each iteration.

`run.py` calibrates the actual initialized property/call target against native
Node and checks causal value/freshness/descriptor/order/frame/binding mutations.
It uses only bounded RAM and emits compact JSON. These samples calibrate the
MODEL; they do not establish a quantified theorem.

`proof.py` prepares the same runtime body with two checked order cases and a
0/1/2 output-prefix invariant ranked by2-index. `Effects.gil` owns the complete
entry/pair field sequences and exact metadata identities; it borrows only the
payload metadata, so arbitrary payload contents remain in the caller frame.
The fixed length2 applies to the mapped root entries, never the payload array.
The default-protocol MODEL assumptions remain additional to this partial heap
PRE; caller World/Lease ownership must establish them before adoption.

For correspondence, relate the source default iterator's index/done to the local
cursor and the same ordinary target. Each source step reads the unchanged length
and same own entry/pair cells, then creates the same descriptor. Primitive keys
invoke no user code; rereading length at the preceding iteration's end is
observationally identical under the unchanged data-only footprint. At cursor2,
both terminate normally. Fresh iterator/result allocations have no escaping
references and are the only hidden resources; all previously owned locations
and the newly returned target remain related. Native samples alone do not prove
this argument or qualify a general iterator implementation.

`Registration.gil` owns the exact ready Object property and callable metadata.
The checked `FERegistered` client reads that actual property, extracts its call
target/scope and invokes it. Its positive proves both body and both client order
cases in the same total run. Eight body controls reject false POST, changed value,
alias, descriptor, order, borrowed input, constant rank and missing rank. Three
client controls reject false POST, returned alias and an unproved dynamic callee.
All twelve controls pass, with 451 definite SMT answers and zero UNKNOWN.
The earlier observer-rejected direct positive remains unaccepted; the fresh
registered positive supplies the qualified body result.

The PRE is one typed two-order union. The two native cases arise by unfolding
that union, avoiding contradictory fixed-order/predicate cross-products. Query
dispatches, files and actual SAT/UNSAT results must join exactly. `raw_unknown`
records the API exception-policy mode, not a solver result; any actual UNKNOWN
still rejects the run. Every selected native verdict is checked by procedure
and case, including genuine POST failures and exact dependency/rank refusals.

Run `proof.py --binary PATH --runtime Gillian-JS/runtime --cases CASES` inside
the pinned runtime image. Select `registered-positive` plus the eleven controls
above; `--cases` uses the names in `CASES`. Each case is limited to 180 seconds;
use 2 CPU, 4 GiB with no swap/network, 512 MiB RAM scratch and a 128 MiB file cap.
No build or dependency copy is needed. Diagnostics are checked then discarded;
the compact outcome is at most 16 KiB.

This ready-binding theorem does not produce startup from `emp`, establish the
default protocol from the partial heap PRE, or repair the old closed Object
World/Lease. The original-normalizer delivery must establish those resources
and adopt this exact capability revision. No N2/public/full-proof completion
follows from this component; publication/integration is recorded separately.
