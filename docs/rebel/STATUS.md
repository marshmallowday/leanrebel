# ReBeL status — M06 carried policy stability in progress; M05 accepted

Resume from remote HEAD of `rebel/m06-carried-policy-20260924`.
Main and earlier proof/review branches remain untouched. All remote access and
checkpoints use the GitHub plugin; no local Git operation is used.

## Current compiler candidate

PolicyStability derives one-player finite-horizon payoff stability from the
largest legal-history action-law L1 distance, retaining the fixed unknown
opponent and canonical chance/simultaneous moves. Full-profile stability uses
the sum of both own-policy distances. No model/actual posterior equality is used.

CFRDPolicyStability measures the actual private resolver's expected own-policy
radius, with zero charge on stopped stages. It derives local replacement loss,
accumulates primitive charges along actual forward memory/history/PBS laws,
and transfers an initial security bound through the complete recursive runner.
CarriedResolvePolicyRates.stepBounds derives the former StepBounds predicate
from primitive action-displacement rates and an explicit total horizon.

This checkpoint is NOT yet compiler/semantic accepted. Both modules are appended
to the analytic root, target list (128) and supplemental all-declaration audit
(90); all old entries and gate behavior are preserved. Next: inspect exact-SHA
M06 compilation; repair any errors; specialize the charge to actual native
carried-PBS depth-solver draws and add nontrivial game-level controls and the
actual noisy-parent security consumer. Do not equate an independent solver's
scalar Nash tolerance with a bound on policy radius.

## Foundation checkpoint

ff51904991ee6fe9bc52feeaf79a8faae16c7c38 is preserved on
`rebel/m06-policy-stability-20260924`. Its M06run35967682504/job107529881979
completed SUCCESS: all126 declared targets compiled and the supplemental
lint/transitive-axiom step completed SUCCESS. The artifact log and independent
full/ReBeL final runs still need exact-source review. FinDistMassDistance and
Examples.MassDistance are unchanged by this successor.

## Earlier accepted evidence and original boundary

M06-status-before-policy-stability.md preserves the exact previous STATUS.
Code46126f37 passed124 targets,86 supplemental modules/1291 declarations and
fullCI35964794518. Independently check ReBeL35964794487/job107520978527 before
counting its whole-workflow completion; it was still running on the last read.
No accepted fresh-chain proof, M05 evidence or printed/corrected Theorem3 audit
is replaced. Source archive digest and initial continuation remain recorded
in M06-policy-stability.md and M06-fresh-chain-validation.md.

The four original M06 parent rows remain pending. Primitive policy-rate
hypotheses are not a proof that the paper's independently recomputed iterates
satisfy a useful vanishing rate. Conditional claims and actual numerical/network
refinement remain distinct. See M06-policy-stability-coverage.md for this slice.
