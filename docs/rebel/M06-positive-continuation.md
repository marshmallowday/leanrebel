# M06: conditional-root zero-reach completion

Source: `GameTheory/Analysis/ReBeL/CFRDZeroReachContinuation.lean`.
The module is registered in the analytic umbrella and the targeted M06 build.
This is an implementation checkpoint, not an accepted milestone.

`cfrDCompleteZeroReach_selected_continuation` proves equality of the complete
canonical continuation laws from any legal history with nonzero original own
reach for the selected players. Each unselected player may use an arbitrary
behavioral policy. Neither their own reach nor joint root reach is assumed
positive. Induction over the remaining horizon obtains positive next-step
own factors from the support of the actual joint draw. Consequently there is
no division by zero and no assumption of agreement at all legal off-path nodes.

`cfrDCompleteZeroReach_positive_continuation` specializes this to completing
all players simultaneously at an all-positive-own-reach root.

This fills the gap between preservation from the initial history and
preservation at a specified conditional root. To connect all-type optimality,
still specialize the selected-player theorem to opponents of a deviator and
combine it with the constructed off-path response and supported-type Nash
optimality. Positivity must be justified on the actual conditional kernels;
ordinary Nash alone does not justify arbitrary off-path kernels or recursive
child quality. Full M06 acceptance remains open.

Read the exact-SHA targeted and full workflow results before recording these
new declarations as verified. Existing negative tests and audit gates remain
unchanged.
