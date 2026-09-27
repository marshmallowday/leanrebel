# M06: native conditional gaps of the actual noisy depth-CFR parent

## Source and scope

Project dependency for ROADMAP M06, not a completion of paper Theorem 3.
Resume latest starting checkpoint 37a4f2c5cc20e285bca054e4a0c544232a218235
through primitive-target acceptance 345bc642284ff51a26a244fd36e47583a77d3879.
The source branch is rebel/m06-depth-native-gap-20260927. Main and earlier source
branches are preserved; no dependency, workflow or validation gate is weakened.

Existing PBSNativeConditionalGap concerns ordinary full-game information CFR.
The actual carried depth sampler instead uses pbsInformationDepthCFRIterate,
whose parent is noisy depth-limited CFR with computed child continuations.
The new module derives native conditional gaps for THAT source and retains its
pbsRootDepthBudget; merely reusing the ordinary CFR budget would be incorrect.

## Exact declaration chain

All core names below are in GameTheory.ReBeL, module
GameTheory.Analysis.ReBeL.PBSDepthNativeGap.

1. pbsInformationDepthCFR_conditional_sampling_value lifts the existing
   supported-history depth-parent sampling law through each supported type's
   original conditional kernel. It holds for arbitrary fixed execution opponent,
   payoff observable and execution horizon, separately from search horizon.
2. pbsInformationDepthCFRConditionalDrawGap defines the conditional best-response
   value minus the sampled own iterate's payoff against the SAME computed
   average opponent. No same-index opponent or changed opponent is substituted.
3. pbsInformationDepthCFRConditionalDrawGap_nonneg derives the sign per legal
   iterate from best-response domination, even for absent types. It does not
   assert per-iterate equilibrium or approximation accuracy.
4. pbsInformationDepthCFRConditionalDrawGap_mean_abs uses that sign and supported
   sampling to equate mean absolute draw gap with the average policy's gap.
   Absolute value is not interchanged with expectation of arbitrary signed noise.
5. pbsInformationDepthCFR_native_mean_abs_le derives the bound from the actual
   pbsInformationDepthCFR_isNash theorem, not a caller-supplied Nash witness or
   root-regret certificate. The bound is the existing pbsRootDepthBudget.
6. pbsInformationDepthBudget_native_mean_abs_le selects the actual positive
   finite parent count using pbsRootDepthBudgetRounds. Its explicit feasibility
   condition retains the noise factor and twice the positive child tolerance.
7. pbsInformationDepthCFRTaggedExecution independently draws the private seed and
   root type, then executes the selected actual depth iterate and retains the
   tags. The arbitrary unknown opponent is fixed and gets no new tag argument.
8. pbsInformationDepthCFRTaggedExecution_tags proves the pre-selection tag law
   is the original product. This is NOT a post-selection independence assertion.
9. pbsInformationDepthCFR_conditioned_native_mean_abs_le selects an actual event
   from that joint tagged execution. The bound divides by the actual positive
   event probability and keeps the joint seed/type query without re-productizing.

The finite full-history and action instances, legal fallback, two-player zero-sum
payoff, absolute payoff bound, uniform prediction-noise bound, positive child
loss and nonzero parent iteration count are explicit where required. No minimum
root-type probability or learner-convergence premise is introduced. Finite-T
residuals remain in the actual depth budget even when prediction noise is zero.

## Controls and validation consumers

GameTheory.Analysis.ReBeL.Examples.PBSDepthNativeGap contains four controls in
GameTheory.ReBeL.Examples.HiddenTypes: depthNativeGap_two_iterates (two actual
noisy parent draws), depthNativeGap_allocated_quarter (computed parent count,
nonzero predictor bias and positive child loss giving tolerance 1/4),
depthNativeGap_certain_query (possible event after actual noisy execution), and
depthNativeGap_impossible_query (no conditioning witness on the empty event).
Both modules are added to the analytic umbrella, existing M06 target manifest
and unchanged per-module lint/transitive-axiom consumer. All original consumers
are retained. Expect 113 explicitly audited target modules and 256 global modules.
These expectations do not substitute for inspecting complete exact-source logs.

Existing adversarial controls remain active: the changed-opponent example in
Examples.PBSNativeConditionalGap, reciprocal-selection sharpness in
Examples.PBSConditionedNativeGap, and unsupported density in Examples.PBSJointNativeGap.
Their generic/canonical scope is not mislabeled as actual solver counterexamples.
Seven independent Fraction tests in test_depth_native_gap.py check sign,
selection-induced correlation, impossible events, feasible allocation and fixed
noise/finite-time terms. All 141 tests passed on the prepared local source based
on exact 35d0 plus these changes; no local Lean executable was available. This
arithmetic check is not Lean verification or concrete C++ equivalence.

## Remaining boundary

The selected gap still uses the ORIGINAL type kernels and the fixed computed
average comparison opponent. Conditioning on an execution event may change both
conditional type kernels and beliefs; that further value transport is not proved
by tag selection. Primitive support smallness for unrestricted finite-T solvers,
changed-PBS native/late value gaps and constructed signed CarriedResolveStepBounds
remain open. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay
pending. M06 remains incomplete. New code is a candidate until its exact source
has successful compilation, normal/slow lint and complete transitive axiom review.
