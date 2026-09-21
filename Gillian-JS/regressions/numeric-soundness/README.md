# JavaScript numeric soundness repair

This fork repairs the demonstrated binary64 rounding false proofs. It is not yet
ready for general JavaScript certification: see the pending integration work below.
Source baseline: `3a1915d6ca74360e74ddd9cccf522e2427f1c70c`.

## What changed

- Encode GIL `NumberType` as SMT-LIB binary64, with round-to-nearest/ties-to-even
  addition, subtraction, multiplication and division, ordered comparisons, numeric
  equality, negation, absolute value and NaN classification.
- Remove real-algebra cancellation, reassociation and conversion distribution
  from floating-point simplification. Integer algebra remains separate.
- Preserve NaN and signed-zero behavior through equality simplification and
  structural expression identity. Solver caches also include the typing context.
- Decode binary64 counterexample models back into GIL numbers.
- Round integer-to-number conversion and truncate finite number-to-integer
  conversion toward zero. The previous symbolic `ToUint32Op` floor approximation
  is now unsupported; it did not implement JavaScript's modulo conversion.

The implementation uses Z3's existing floating-point theory:
https://smt-lib.org/theories-FloatingPoint.shtml.

## Validation

The source-built fork passes these controls (`patched-results.json` records hashes
and results). Negative cases must fail at their assertion or postcondition;
exceptions, timeouts, missing paths and exploration cutoffs do not pass.

| Case | Expected result |
|---|---|
| `number-rounding.js` | Accept: `2 ** 53 + 1` rounds back to `2 ** 53`. |
| `number-symbolic-monotonic.js` | Reject: `n + 1 > n` is false for an admitted input. |
| `deductive-number-monotonic.js` | Reject the same false postcondition. |
| `deductive-number-step-two.js` | Accept the valid `n + 2 > n` postcondition over that range. |
| `number-overflow-nan.js` | Accept overflow to infinity and subsequent NaN inequality. |
| `number-signed-zero.js` | Accept positive zero after adding positive zero. |
| `number-signed-zero-fail.js` | Reject the claim that equality to zero fixes its sign. |
| `heap-alias.js` | Accept an ordinary symbolic heap alias update. |

The core suite adds 484 direct solver comparisons against native binary64
arithmetic (four operators over 11 x 11 boundary-value pairs), plus symbolic
rounding, conversion, equality, simplification, cache and model-replay checks.

`baseline.json` preserves the original published-image observations. That image
is not independently attested as this source commit. An unmodified source build
of the commit above was also checked with the same OCaml 5.3 / Z3 4.13.3 toolchain:
it incorrectly accepted the deductive monotonicity claim. The patched build
rejects that claim with `Couldn't satisfy postcondition` when verifying
`--proc increment`.

## Reproduce

From the repository root, with the OCaml dependencies and Z3 available:

```sh
opam install ./gillian.opam ./gillian-js.opam --deps-only
dune build -p gillian,gillian-js
dune runtest GillianCore
GILLIAN_JS="dune exec --root $PWD -- gillian-js" \
  python3 Gillian-JS/regressions/numeric-soundness/run.py
```

The runner creates an isolated temporary directory for each case, retains logs
and writes a result manifest. `GILLIAN_JS` may also name an installed executable.
Verification cases explicitly select their named procedure; they do not validate
the bundled runtime lemmas. Every run has a 60-second process limit.

Concrete JavaScript witness:

```js
const n = 2 ** 53;
console.assert(n + 1 === n);
console.assert(!(n + 1 > n));
console.assert(n + 2 > n);
console.assert(1 / -0 === -Infinity);
```

## Pending integration work

1. **Unrestricted verification has a regression.** Normalizing the bundled
   `ArrayOfArraysOfUInt8ArraysContentsAppend` lemma now reaches a mixed
   integer/binary64 query that Z3 4.13.3 cannot decide. The CLI fails during lemma
   preprocessing. The unmodified source succeeds at that preprocessing stage.
   The minimal query in `mixed-integer-float.smt2` reproduces `unknown` directly
   in Z3; the reported reason is incomplete arithmetic. Resolve this conversion
   integration before treating the fork as a general replacement. Explicitly
   selecting a procedure only scopes the regression tests; it does not fix this.
2. **The remaining numeric/runtime surface is not certified.** Several numeric
   operators remain unsupported, string/number conversions remain uninterpreted,
   and `NumToInt` now requires a finite concrete operand at the SMT boundary.
   Symbolic or non-finite operands fail closed until symbolic execution supplies
   a finiteness obligation and models the conversion fault.
   Bundled runtime specifications and other consumers of numeric equality need
   a broader audit. This patch does not claim complete backend soundness.
3. **General execution and termination remain separate work.** This patch changes
   Gillian's numeric machinery; it does not establish complete-fold proofs or
   production lowering correspondence.
