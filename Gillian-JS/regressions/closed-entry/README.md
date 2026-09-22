# Closed entry verification

`verify FILE --total --closed-entry --proc=main` checks a single parameterless
entry with one normal `emp` precondition. Its result states that execution from
the empty initial state terminates and establishes the postcondition. It is not
a frameable procedure summary, is not made available to callers, and is not
written to the incremental verification cache.

This permits fresh fixed-name JS runtime allocations: the complete heap is
exposed throughout execution, and an existing name is rejected. Heap abstraction,
resource production, lemma applications and assumptions are forbidden, including
inside macros. Checked pure assertions, macro conditionals and global unfolding
remain available for compiler-generated lookup tactics; there are no folded
predicates to expose. Ordinary totality and exploration checks still apply.
Generated concrete allocation names are reserved in executed expressions and
postconditions, including predicate definitions. Ordinary procedure verification
continues to reject fixed-name allocation.

The controls cover correct and false postconditions, heap contents, nested
calls, collision, hidden resources, generated names, entry selection, parameters,
assumptions, cycles and attempts to use procedure summaries. The PoC separately
checks the actual AJV wrapper with the full `Init.jsil` initializer: verification's
default minimal initializer does not create the required standard built-ins.
