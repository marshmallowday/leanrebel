# M06 zero-own-reach completion

Continue on `rebel/m06-recovery`. The core child adapter passed target run
`35476596169` at `50953465`. The live-child controls compiled in run
`35476945793` at `538c0866`; the full architecture gate correctly rejected a
new `change` tactic in the frozen Analysis transport budget. `dfd2d861`
replaces that step by definitional simplification; no audit budget is changed.

## Source review and proof boundary

The ReBeL arXiv v2 supplement, printed pages 21-22, couples the parent
iteration's leaf values to recursively computed child play and then delays
private iteration draws. Its printed delta-scaled finite-T term remains
separate from the corrected additive finite-T bound used here.

Burch, Johanson and Bowling, Solving Imperfect Information Games Using
Decomposition, arXiv:1303.4441v4, Theorem 2 and the discussion on PDF page 5,
requires counterfactual best responses, explicitly distinguishing them from
ordinary best responses at zero-own-reach information sets. That discussion
also describes completing zero-own-reach decisions after an equilibrium
solve. Both papers were checked from their primary PDFs during this stage.

## New proof operation

CFRDZeroReachCompletion makes that completion information-local by testing
informationOwnReach, not actual hidden state, joint reach or opponent reach.
Induction on legal traces proves preservation of the complete own-reach
function. Canonical probability factorization then proves preservation of
on-policy play, play against every fixed opponent, every unilateral deviation
against the completed opponents, and the ordinary Nash predicate.

The completed child average therefore retains the exact delayed-sampling law
while allowing the counterfactual continuation at zero-own-reach states to be
chosen separately from the deterministic averaging fallback. No positivity
of the current strategy is assumed and no test or trust gate is weakened.

This operation alone does NOT prove optimality of an arbitrary completion.
Construction and verification of the child solver and its counterfactual
completion remain separate. In particular an on-policy or Nash preservation
theorem is not silently relabeled as that missing optimality proof. The new
module is registered for target and recursive full validation; inspect its
exact-SHA compiler results before counting it as verified. M06 remains open.
