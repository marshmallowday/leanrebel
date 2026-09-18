# M04 unilateral averaging checkpoint

At 6781fb3a3fc018575e073e878d6cee544ae11fb3, actual ReBeL run
35310573421 / job 105491585375 compiled RootRegretBounds, including the
uniform whole-policy CFR bound, plus all prior coupled-table/payoff/own-reach
modules. It failed only in OutcomeReach on an unused simp argument and the
noncomputable decision in a theorem's cut predicate. This checkpoint removes
the unused argument and makes that specification decision explicit. It does
not add a decidability hypothesis to the game or relax any validation gate.

UnilateralAverage connects the own-reach average to expected outcome laws
against arbitrary fixed opponents. For a structural two-player carrier it
then preserves every unilateral deviation against the averaged opponent.
This is stronger than on-policy outcome equivalence and is the needed bridge
from the finite-time regret bound to canonical approximate Nash.

New sources are pending their own compiler/lint/axiom results. M04 is not yet
accepted: canonical Nash, the executable rational solver and real refinement,
and independent exhaustive best-response/boundary tests remain required.
The exact branch, source and validation evidence must be checked on restart.
