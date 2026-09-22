# Defined predicates in total verification

Run `GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/predicate-totality/run.py`.
Expected failures require their exact exit/message; a timeout or unrelated crash
cannot pass. `observations.json` identifies the tested source and binary.

Total mode admits fold/unfold of defined, unguarded predicates and applications
of fully checked lemmas. Folding consumes the definition; unfolding produces
all feasible alternatives. Production errors remain obligations, including
when another alternative succeeds. Recursive unfolding has a finite proof budget;
exhaustion reports unsupported analysis, never success or a program counterexample.

Author `facts:` are ignored in total mode. Adding them to definitions would
silently strengthen admission, so definitions are kept unchanged. Type facts
introduced by preprocessing are justified by identical constraints added to every
definition. A `pure` annotation can permit duplication only when every reachable
predicate definition is resource-free; native heap predicates, guarded/abstract
predicates, magic wands and aliases to them do not qualify. This is a conservative
structural check, not an inference that arbitrary predicate facts are true.

The controls cover valid heap folding, disjunctive alternatives, a checked
natural-induction lemma, false facts, resource duplication through false purity
and aliases, false folds/posts, guarded predicates and unfolding exhaustion.
Ordinary verification retains its legacy author-hint behavior. These controls do
not establish general matcher soundness or the full compiled-JavaScript theorem.
