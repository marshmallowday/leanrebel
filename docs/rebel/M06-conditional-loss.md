# M06 approximate child continuation: probability budgets

Restart source: b5e15493d6efdc4fa641aeb690e40b24a0764d11.
Scope: ROADMAP M06, SEARCH-ERROR and SEARCH-CFRD dependency, not acceptance.
Source: GameTheory/Analysis/ReBeL/PBSApproximateOptimality.lean.

Canonical approximate Nash controls the mean conditional best-response gap
because one legal remembered-type response attains all these maxima. Gaps are
nonnegative. Hence each own-type probability times its gap is at most epsilon.
For positive probability p the bound is epsilon/p, not epsilon. If the child
solver uses a root budget epsilon <= p*loss, its typewise loss is at most loss.
Absent types require the existing constructed zero-own-reach response instead.

The four new theorems quantify over full legal behavioral deviations and use
canonical PBS execution, finite-plan attainment and remembered-type splicing.
They do not assume a root decomposition or a conditional-value inequality.
The approximate Nash hypothesis itself still requires a finite child solver.

Coverage journal: SEARCH-ERROR gains a probability-aware approximate-child
bridge; SEARCH-CFRD and SAFE-THEOREM3 still need its instantiated solver and
recursive execution. All parent rows and inherited exact-driver evidence are
unchanged. This source checkpoint is not verified until its exact-SHA build,
examples, lint and transitive axiom output have been inspected.
