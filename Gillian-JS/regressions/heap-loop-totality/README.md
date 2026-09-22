# Heap measures and compiled JavaScript loops

`run.py` checks owned heap counters, arbitrary finite logical-list traversal,
relational accumulation, incoming-edge PHI selection, and actual compiled
JavaScript `while`/`for` loops. JavaScript numeric controls cover the complete
native array-length range. This is proof-rule coverage, not the original
classifier theorem or a proof of the verifier implementation.

The loop rule matches the invariant against the current state before evaluating
its measure. On a back-edge, the match substitution supplies the current logical
heap values; descent is checked against the separately frozen entry measure.
On first establishment, generalization precedes freezing. Input, suspended
caller and outer-frame identities cannot be rebound as fresh loop existentials.

Every modified live program local is generalized using the existing invariant
binder mechanism, even when omitted from the annotation. Such a local must
already exist on the actual incoming path. Liveness selects PHI operands using
the interpreter's predecessor table and respects the interpreter's sequential
PHI assignments. Missing incoming values remain execution failures. A PHI-only
entry prefix can precede a ranked invariant; executable updates cannot be
smuggled into that prefix. JavaScript total-mode compilation places the loop's
completion-value PHI before the invariant without reordering executable code.

The runtime's terminal `assume(false)` helpers require a narrow CFG treatment:
it has no successor, but remains forbidden if reached on a feasible proof path.
The helper suite includes both reachable and unreachable controls. No assumption
is licensed by the CFG treatment.

Negative expectations require the intended diagnostic as well as exit status;
crashes or timeout exit codes alone never pass. Ordinary proof failures are not
automatically concrete counterexamples. See the PoC's ordered verification
backlog for the remaining logical-size, UTF-16, JSON and AJV obligations.

Shared metadata survives matching in the saved loop frame. The abstract state
retains only overlapping core facts, and location simplification keeps saved
frame and caller identities as representatives. Exclusive cells remain framed.
Controls cover arbitrary countdowns, changing metadata fields, nested loops,
restored outside cells and suspended caller pointers, plus wrong results,
stalls and forbidden access to a framed cell. Distinct protected locations
cannot be silently merged. This repair is exercised by the actual runtime
Array.push proof in the PoC.

Resource matching uses `v==` value identity. It preserves signed zero, accepts
NaN identity and compares nested values through native SMT datatype equality.
Numeric `==` remains IEEE comparison. Generated store and lemma bindings use
identity; author-written numeric equalities remain constraints, including both
zero signs, in preconditions and produced procedure summaries. JavaScript and
JSIL proof annotations also accept `v==` for exact ghost bindings.

The controls retain false signed-zero postconditions and a countdown that
incorrectly claimed canonical positive zero. The valid countdown permits either
zero sign and preserves its returned/stored identity. They also cover NaN,
nested descriptors, predicate inputs/outputs, numeric versus exact bindings and
summaries, and an unrestricted-Number segment lemma. A NaN assertion previously
made preprocessing loop because its fixpoint used OCaml numeric equality;
structural assertion equality now decides convergence.
