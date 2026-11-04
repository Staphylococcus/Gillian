# Selected default-array Object.fromEntries MODEL

This is an unqualified N2 capability candidate, not arbitrary iterable support.
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
It uses only bounded RAM and emits compact JSON. Calibration is not quantified
proof: capability qualification still requires the actual body/loop contract,
complete definite proof accounting, meaningful POST controls and independent
review. All acceptance flags remain false here until those checks exist.
