# M06 approximate child continuation: probability budgets

Restart source: b5e15493d6efdc4fa641aeb690e40b24a0764d11.
Scope: ROADMAP M06, SEARCH-ERROR and SEARCH-CFRD dependency, not acceptance.

PBSApproximateOptimality derives mean and probability-weighted conditional
best-response gaps from canonical approximate Nash and a single legal
remembered-type response. For positive type probability p the bound is
error/p, not error. A root budget error <= p*loss yields conditional loss.
Zero-probability types are not certified by the weighted inequality.

CFRDApproximateLeaf connects this result to joint zero-own-reach completion,
legal public-response splicing and the actual constructed reference table.
Factual queries use probability-budgeted approximate PBS Nash. Nonfactual
queries use the existing constructed conditional best response at zero own
reach. The resulting theorem concludes CFRDLeafOptimal at the stated loss,
without assuming a conditional payoff inequality or kernel-identification data.
The approximate child Nash premise still needs a finite-iteration constructor;
this checkpoint does not claim that the finite child algorithm is implemented.

Examples/CFRDApproximateLeaf uses the existing canonical two-player type-plan
matrix game to exhibit root error p with conditional gain one, for arbitrarily
small positive p; at p=0 even exact root Nash leaves that gain unconstrained.
A separate live HiddenTypes example applies the new reference-table theorem
to the existing constructed exact child (zero-error specialization), including
all reference queries and arbitrary legal behavioral deviations.

All three modules are registered in the public analytic root, target list and
supplemental transitive-axiom/normal/slow-lint consumer. Existing gates remain.
The first checkpoint 594cfc65 failed target run 35507002570/job 106068402421:
a redundant simplification, the orientation of addition in the final linear
inequality, and an erroneous Examples prefix on CFRDResolveBelief in the target
list. The next checkpoint repairs those errors, retains the actual inherited
target and adds the approximate contract and controls. No theorem is weakened.

Coverage journal: SEARCH-ERROR gains probability-aware continuation transport;
SEARCH-CFRD and SAFE-THEOREM3 still need the instantiated finite child solver
and fresh recursive carried execution. Parent rows and inherited exact-driver
evidence remain unchanged. Exact-source compiler/lint/axiom feedback and
semantic review of the new examples are required before acceptance.
