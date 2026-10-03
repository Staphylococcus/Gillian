# Internal enumeration cursors

The compiler's `for…in` state and Object.jsil prototype-copy loop consume a
remaining-key List. Neither uses a binary64 counter, which stops progressing
when adding one at `2^53`. Visible JavaScript Number arithmetic is unchanged.

Run compiler structure/header checks with `for_in_cursor_tests.exe`, then:

```sh
python3 Gillian-JS/regressions/enumeration-cursors/run.py
gillian-js verify Gillian-JS/regressions/enumeration-cursors/entry.js --total --proc=CursorStep
```

Set `GILLIAN_JS` to the actual compiler command and `GILLIAN_RESULTS_ROOT` to
a fresh evidence parent. The sixteen execution controls exercise empty Lists,
own/numeric order, nested and labelled jumps, early return, prototype shadows,
non-enumerable shadows, deletion, null/undefined, ordinary numeric loops and
the unchanged Number stall. The false ordering result must throw the explicit
result-mismatch value, rather than pass through an empty or skipped traversal.

An uninstalled binary needs `-R` pointing to its matching installed runtime.
The existing loop-soundness family is also an affected regression: its three
ForIn fixtures explicitly import a sibling `Object.jsil`, so prepare those
fixtures with the matching runtime file before verifying them. The ordinary
nineteen cases require no such sibling.

`CursorStep` proves that consuming one key strictly reduces the exact integer
List length for every typed finite tail. The false unchanged-result post and
unchanged-cursor body both fail their postconditions. This focused primitive
does not discharge the prototype-copy heap invariant or recursive dependencies.

These are compiler/runtime regressions, not a full-domain Object or AJV theorem.
Whole-ownership contracts, natural ranks for reached loops and all checked
dependencies must still establish the original validator's total correctness.
