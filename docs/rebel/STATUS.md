# ReBeL status — M06 in progress; M05 accepted

## Active implementation restart

Continue on `rebel/m06-counterfactual-envelope-20260921`; read its actual HEAD.
The base is ce55384a01cd91b6d8070314074f46690462a25f, preserved on the prior
refresh-checkpoint branch. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
M06-status-before-envelope.md preserves the preceding STATUS with identical
blob 3912632e8a153cfe02a603b078e5165461aa2520. No old work is replayed.

## Restart validation and current source boundary

Base full repository CI 35535912944/job 106144785492 succeeded. Base full
ReBeL run 35535912927/job 106144785441 also completed successfully after the
initial observation: its downloaded log ends REBEL_VALIDATION_PASS modules=177.
Artifact 10613288740 has ZIP SHA256
ffd42a08804cc4789209b0ffddafd73c1cc96f26d5820b870b368011575b3b99.
These exact-base successes do not validate new proof source.

The initial envelope target 12f801cd, run 35537380417/job 106148766723,
compiled the stopped-fiber, reweighting and prefix-comparison proofs but
rejected the retained control's un-eta-expanded function rewrite. Its repair
uses functional extensionality, without changing the theorem statement.
All new sources below require this commit's target, normal/slow lint,
architecture and transitive axiom checks. No success is inferred from presence.

## Source-directed proof bridge

CFRDResolveEnvelope compares the resolved OPPONENT payoff with the incumbent
MODEL continuation on every positive opponent-reference information fiber.
Perfect recall transfers this envelope to the actual unknown-opponent prefix.
Stopped fibers have zero gap. Accuracy and a child-value upper bound combine
additively on the same reference law; no factual posterior is invented.
CFRDEnvelopeSafety combines focal full regret with opponent PREFIX regret,
both instantiated from the actual depth-limited CFR-D recurrence, to prove
V_ref - (A*predictionError + C/sqrt(T) + focalChildLoss + envelopeLoss).
There is no refresh probability penalty or fixed-opponent retention premise.

The local envelope is STILL an explicit recursive solver obligation. It is
not obtained from two independently selected Nash policies. Current controls
instantiate the bridge with actual noisy finite-child retained policies and
separately show, in the canonical replacement game, that a universal opponent
model ceiling does not imply preservation of exploitation against a fixed
weak opponent. A bad legal candidate fails that ceiling. The original
counterexamples and bounded-refresh variant remain intact.

## Remaining construction and coverage

Construct a source-consistent recursive child table whose test-time strategy
meets the opponent-reference envelope, including zero-factual-mass fibers and
multiple actual carried PBS levels. Do not substitute a final security bound
as data or assume an unknown opponent equals the model belief. The reference
finite children remain adaptive complete-plan normal-form solves, distinct
from the paper's information-set CFR and executable numerical refinements.
Keep prediction, child, outer-iteration and optional replacement losses
separate, and keep printed and corrected Theorem 3 distinct.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
This source-directed bridge advances dependency depth, not full M06 acceptance.
All original coverage identities, M00-M05 evidence and gates are retained.
