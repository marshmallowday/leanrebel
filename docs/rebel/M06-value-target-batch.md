# M06 root value-target and frontier batch

Base e123cb860ce0a56c2705a375b9ff1e403f7580be was accepted on all four
Actions workflows (M06-summary-coupling-e123cb8-accepted.md). The current
work branch is rebel/m06-kernel-value-repair-20260927, selected because its
accepted implementations, M06 ledger and continued repair history are here.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
The chat's initial baseline is 9457c198126f3c8b7cb1045bbed2e0053788636f.
New source below is PENDING its own exact-SHA Actions.

## Why this batch and order

Review of the original M06 inventory found an explicit output gap:
P-CFRD-TARGET and P-CFRD-AVERAGE require root information-state value
vectors from each iteration and their uniform mean. Previously the coupled
policy/leaf-value solver had no named root-target output. This batch adds
the finite-law error proof, actual coupled-trace target, uniform accumulation,
constructed noisy-root integration and controls together. It also records
completed frontier source review, whose code is unchanged and already
validated at the base. Small-cost independent re-solving is a different
unresolved mathematical boundary; it is not assumed to complete these outputs.

## Computation and proof chain

1. terminalExact_root_error conditions on a root label measurable in the
   player's leaf information. The density is constant within each information
   fiber. Conditional value errors therefore remain bounded by delta even
   when individual hidden-history residuals are large, with no inverse-mass
   amplification. Terminal contributions remain exact.
2. cfrDDepthValueTarget uses the actual cfrDDepthPlay and the prediction from
   the matching cfrDDepthQuery. It runs only the searched prefix and backs up
   predicted live-cut values or actual terminal utility. It does not evaluate
   the full continuation during target computation. cfrDDepthExactTarget is
   the proof-side comparator using that same round's continuation.
3. cfrDDepthValueTarget_error transfers the actual dominating reference
   contract to factual live fibers and then each information-local root
   label. The support set is explicit. Total absent-fiber entries use the
   original-law fallback and are not represented as observed training samples.
4. cfrDValueTargetMean retains each vector coordinate and uses exactly rounds
   zero through T-1. The sum identity, initial round, online uniform update
   and non-amplification of numerical error are proved. No empty sampling
   law is introduced.
5. pbsRootValueReadout retains the administrative root observation in the
   full AOH. Its snapshot theorem identifies the original own information,
   including distinct own types without a hidden-world input. The rooted
   target has cut+1 fuel, accounting for the administrative step.
6. pbsRootDepthValueTarget and its mean use the existing actual noisy,
   finite-information-child parent. Accuracy is derived from the explicit
   uniform noise bound through cfrDConstructedInformationOracle_accurate;
   no per-iterate Nash or root-value certificate is supplied.

## Source and acceptance boundary

The [main paper, section 5.1 and Algorithm 1](https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf)
describes iteration-specific root vectors and uniform target accumulation.
The [supplement, Algorithm 2](https://papers.nips.cc/paper_files/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Supplemental.pdf)
also discusses a practical linear weighting and warm start; that schedule is
not silently substituted for the main-paper uniform mean here.

This proves numerical propagation relative to the mean of actual per-round
conditional continuation values. It does NOT prove that these target vectors
converge to a unique equilibrium information value, equal the value of
independently averaged joint policies, or train a convergent network.
Zero-probability root entries need the stated support convention; they are
not unconditional posterior assertions. The general root-label API requires
an information-local readout; the constructed-root API supplies one.

The unchanged frontier modules now have exact-source acceptance for
SEARCH-FRONTIER, P-SEARCH-SETUP and P-SEARCH-LEAF, recorded in
M06-frontier-accepted.md and coverage-updates/M06-frontier.json.
P-CFRD-TARGET/P-CFRD-AVERAGE and their parent remain pending until the new
source passes Actions and the remaining supported-root/source correspondence
is reviewed. SEARCH-ERROR and SAFE-THEOREM3 are not promoted.

## Controls and validation surface

Examples/CFRDValueTarget checks the genuine hidden-type noisy finite-child
parent's mean with bias 1/8, unchanged own-information labels across hidden
opponents, and a separate two-coordinate arithmetic control that differs
from the last vector. Seven independent Fraction tests cover rare-root
conditioning with large hidden residuals, terminal/exhausted bypass, absent
labels, online vector means, numerical error, joint-iteration correlation,
root memory and changed noisy learning traces.

The umbrella, target manifest and exact-source audit register both new
modules. Expected surface is 158 targets, 120 targeted / 263 global audit
modules, and 176 Python tests. Existing modules/tests remain. All workflows,
audit standards, axiom allowlist and the frozen historical coverage blob are
unchanged. No Lean, lint, axiom or Python test was run inside the plugin.

Remaining M06: useful small-cost bounds for actual independent recursive
solves, complete recursive application of stored-model kernel comparisons,
source-specific target/algorithm review and remaining SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 acceptance. Keep printed R5 and corrected/
restricted results separate; finite-T residuals and child tolerance remain
visible and no learner convergence is assumed.
