# M06 carried belief after re-solving

## Validated target checkpoint

All declared M06 targets, including the generic resolver, its finite-time
security connection, the live positive and negative controls, and the
belief-carrying step compile at
`667b6acbff132ef49d84b05574c94e5554312020`. Targeted run `35473013919`, job
`105977329014`, succeeded. Full compiler/lint/architecture/axiom acceptance
is separate; it must be inspected for the exact proof commit.

## Model belief and private draws

CFRDResolveBelief extends the saved resolver execution with the newly selected
private profile and its updated MODEL PBS. Updating starts from the stored
joint belief, executes the selected future model from those histories, then
conditions on the new public observation. It does not replay the new profile
from the original initial state or insert the actual unknown opponent into
the model posterior. Missing model support remains explicit as None.

The public history can only extend the carried public past. Projecting away
the new model/private state gives precisely the existing canonical resolver
outcome law, and hence preserves the previously derived payoff/security
statement. The public positive/negative controls remain distinct: the fair
resolver supplies its local comparison for every opposing policy in the live
hidden-type game. The wrong constant resolver loses one unit at an explicit
legal continuation history. It is not claimed to be a recursively computed
CFR-D or equilibrium resolver.

## Finite execution chain: next compiler checkpoint

CFRDRecursivePlay carries the original private iteration and every newly
drawn model profile through a finite sequence of actual resolver steps. Each
step uses the stored PBS and preserves the original unknown opponent.
The finite schedule terminates structurally; zero-fuel and terminal stages
use the already defined no-query rule. Empty schedules recover the original
private carried continuation exactly.

The accumulated-loss theorem assumes named, reached-state LOCAL comparisons
between the old selected continuation and the newly selected continuation.
It does not assume the value of the remaining recursive program. Induction
on the actual forward state laws derives the sum of stage allowances and
transfers any previously established lower bound to this finite execution.
These are compiler targets until the new exact-SHA results are inspected.

## Remaining M06 obligations

The stage-local comparisons and CFRDResolverLocal are not automatic from
ordinary on-path Nash equilibria. General recursive PBS solving and the
derivation of its counterfactual continuation/replacement contracts remain
required. The new finite-chain execution/composition is not a substitute for
constructing those child solvers and proving their contracts. No coverage
row or M06 acceptance status is promoted in this checkpoint.
