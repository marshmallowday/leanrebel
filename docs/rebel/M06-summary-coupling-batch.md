# M06 constructed summary couplings and stored-posterior comparisons

## Selected continuation and batch boundary

Continue rebel/m06-kernel-value-repair-20260927 from the re-read HEAD
d54ec59cfaa17a117a9a720d1b85ba64842f4315. The previous repair loop is fully
accepted at this SHA; see M06-signed-kernel-d54ec59-accepted.md.
Default main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
The GitHub plugin reports account marshmallowday, repository admin/push
permissions, and collaborator admin permission. This existing M06 branch
contains the pending work, so no main commit or unrelated branch is needed.

The next batch combines finite-law coupling construction, signed recursive
consumers, concrete posterior comparison, examples and independent controls.
These are implemented together before one commit. The next boundary is
deriving the new sufficient conditions from the actual unrestricted solver:
equality of observable laws is not implied by scalar Nash accuracy, and no
new assumption is silently inserted into the original M06 specification.

## Construction and integration

- FinDist.summaryCoupling draws the first outcome and conditions the second
  law on its observed summary. summaryCoupling_fst is unconditional.
  summaryCoupling_snd proves the second marginal from equality of the complete
  summary distributions. summaryCoupling_support proves both original support
  memberships and equality of summaries; unreachable fallback fibers receive
  no mass under that premise.
- directedValueCost_summaryCoupling_le derives a cost from the supported
  payoff diameter of matched summaries. directedValueCost_summaryCoupling_payoff
  constructs a zero-cost witness for equal payoff distributions, including
  nonconstant payoffs and disjoint history supports. Equal means are not enough
  for this construction, and no supplied low-cost coupling is assumed.
- carriedResolveStepBounds_of_summary constructs the existing signed step
  certificate from those observable laws and pairwise payoff bounds.
  carriedSignedSequenceLoss_le_summary bounds the exact native signed sum.
  privateRecursiveResolve_inherits_summary transfers an initial security
  bound through the actual private-prefix law. Finite-T, oracle and child
  errors already present in that initial bound are retained.
- resolvedNextState_conditionalGap_le constructs BOTH slices from the incoming
  joint PBS and the actual next state's stored model posterior. Supported
  old kernels become own-type conditioning of the incoming PBS; supported
  new kernels become public-then-type conditioning of the selected model's
  canonical continuation. It directly consumes the changed-kernel AND changed-
  opponent gap bound. Type domains may differ. Absent new types are not assigned
  a fictitious conditional. This is a per-step comparison interface, not a
  claim that every global recursive solver comparison is now discharged.
- The existing nonconstant, disjoint-support control now constructs its
  coupling from marginals and payoff observations; it no longer needs the
  earlier manually provided witness for this consumer.
- The actual two-stage noisy depth schedule consumes the summary construction
  and derives total allowance 2*error. Its common-observation and supported
  payoff-range premises remain explicit. Unknown opponent and hidden state
  remain proof-side parameters, never new resolver inputs.

The native solver, private draw, posterior update, and execution schedule are
unchanged. The coupling is an analysis witness; it does not independently
resample either executed private draw or the actual state at stage boundaries.

## Independent controls and pending validation

Five new Fraction tests cover:
1. Ten exact-marginal cases with split fibers, absent labels, nonconstant
   payoff, zero directed cost and maximal history-label variation.
2. A same-mean/different-distribution negative control, and incorrect second
   marginals when complete summary-law equality is absent.
3. Nine positive bin-diameter cases, sharp cost and reverse-direction zero cost.
4. Twenty-seven native two-stage cases with positive late fuel, retained private
   draws and forward-state weights; the large initial-label payoff is preserved
   while the smaller tail payoff incurs at most two bin diameters.
5. Eight stored-model posterior/type/response comparisons; explicit double
   conditioning and the kernel gap inequality, with factual posterior inequality.

All 13 added public Lean declarations were checked against the accepted 5129
declaration names for collisions. Existing modules are extended; no module or
target is removed. The five edited Lean modules remain reachable through the
existing 156 build targets and 118 targeted/261 global audit modules.
Expected Python tests increase from 164 to 169.

This is source review, not a claim to have run Lean or Python locally.
New-source build, full lint and complete transitive axioms, architecture,
rational runtime and Python checks remain pending the new SHA's Actions.
Current push filters cover the branch and both Analysis/Probability paths.
Workflows, validation scripts and historical coverage.json are unchanged.

## Original obligations still open

A constructed low-cost witness is now available under observable-law matching,
but that premise and useful payoff diameters still need derivation for the
unrestricted noisy recursive solver. Do not promote original source obligations
on the strength of conditional dependency theorems. Apply actual stored-PBS
comparisons throughout the remaining recursion and discharge the small-cost
or alternative signed-envelope conditions.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 still require
source correspondence and acceptance. Keep printed R5 distinct from corrected/
restricted bounds, retain finite-T error at zero prediction error, and do not
assume learner convergence. M06 remains incomplete.
