# Closed entry verification

`verify FILE --total --closed-entry --proc=main` checks a single parameterless
entry with one normal `emp` precondition. Its result states that execution from
the empty initial state terminates and establishes the postcondition. It is not
a frameable procedure summary, is not made available to callers, and is not
written to the incremental verification cache.

Before any invariant executes, this permits fresh fixed-name JS runtime
allocations: the complete heap is exposed, and an existing name is rejected.
Checked ranked invariants may then abstract owned resources into predicates and
loop frames. Explicit unfolding exposes only already-owned predicates. From the
first executed invariant onward, **all constrained allocations are unsupported**,
even distinct fixed names or allocations after loop exit; only `Alloc(empty, …)`
remains available. This prevents an allocation from colliding with an object
hidden by abstraction. The phase is conservative across symbolic sibling paths
and scoped to one verification invocation, with reset/restoration on exceptions.

Resource production/folding, lemma applications and assumptions remain forbidden,
including inside macros. Checked pure assertions, macro conditionals and global
unfolding remain available for compiler-generated lookup tactics. Ordinary
invariant establishment, preservation, rank, definedness and frame checks apply.
Generated concrete allocation names remain reserved in executed expressions and
postconditions, including predicate definitions. Ordinary procedure verification
continues to reject fixed-name allocation.

The controls cover correct and false postconditions, heap contents, nested
calls, collision, hidden resources, generated names, entry selection, parameters,
assumptions, cycles and attempts to use procedure summaries. The PoC separately
checks the actual AJV wrapper with the full `Init.jsil` initializer: verification's
default minimal initializer does not create the required standard built-ins.
