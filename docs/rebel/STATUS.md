# ReBeL status — M06 in progress; M05 accepted

## Resume from the conditional-value stability checkpoint

Work branch: rebel/m06-conditional-value-repair-20260925.
Initial implementation source: 069bb7e91eab35772670fc6e060d90f42e58ac07 on
rebel/m06-conditional-value-stability-20260925. That source is preserved so
its already running CI can finish. The repair adds explicit unfolding of
canonical expected-utility preference in the exact-Nash negative control;
it changes no theorem statement, assumption, target or audit policy.
It was identified in source review, not reported as an observed CI failure.

Parent checkpoint: d2cb889b5538bc9429eb47a7a7e32309d0e31bb7 on
rebel/m06-scalar-checkpoint-20260925. Read
M06_CONDITIONAL_VALUE_STABILITY.md and M06-conditional-value-stability-coverage.json.
Main and predecessor branches are unchanged. The new source is pending
exact-SHA compiler/lint/axiom results; no completion or acceptance is claimed.

## New dependency-closed M06 slice

PBSConditionalValueStability proves a conditional self-payoff comparison
at one fixed TypeBeliefSlice when every opposing policy coordinate agrees.
The weighted absolute error is at most the MAXIMUM of the two root Nash
errors. The unweighted bound divides only on supported types. Zero type
mass masks the root inequality; it does not make off-path kernels zero.

The actual information-set CFR interfaces derive their own approximate
Nash premises. The two-output comparison retains the explicit same-opponent
premise. The budgeted single-output theorem instead compares against that
output's CURRENT-opponent Eq. (1) value. No independently changed opponent
is identified with it. A live HiddenTypes solve at budget 1/8 instantiates
this conditional bound. A finite canonical zero-sum type-game counterexample
has exact root equilibria but conditional value drift one when opponents
change. Rare/absent-type predecessor controls remain intact.

Both new modules are in the umbrella, existing M06 targets and explicit
exact-leaf audit. The unchanged repository-wide ReBeL checker discovers
them too. See the companion coverage file for declarations and the review
for premises, source scope, validation status and remaining work.

## Initial-source checks and exact identities

Source 069bb7e was exported by the GitHub plugin from artifact10858392547
of ReBeL run36122178162, source job108030091662. The ZIP and source tar
hashes and embedded commit were checked before inspecting its bytes.
On that exact source export all83 Python tests, ledger/inventory structure
checks and the complete public Lean line-width scan passed. The three
integration lists each add exactly the two new modules; none is removed.
These checks do not compile or certify Lean proofs.

Initial targeted run36122178153/job108029971904 and independent ReBeL
run36122178162/job108030091929 were still compiling when re-read.
The latter had passed preliminary architecture, ledger and rational runtime
checks. These are not final success claims. The repaired source requires
its OWN exact-SHA compiler, lint and axiom evidence; do not substitute the
initial-source or parent checks. Consult branch-head Actions before resuming.

## Predecessor validation resolved

The scalar source is 5a9fc55e6b944abb16ec7f2e16e80deb0db341f3 on
rebel/m06-scalar-tail-repair-20260925. GitHub compare confirms the two
commits from there to d2cb889b changed only eight documentation files.
Independent ReBeL run36113477739/job108001998664 is now completed SUCCESS:
architecture, ledger, rational runtime, complete ReBeL compilation,
transitive axiom audit, lint and cleanliness all passed. Source snapshot
job108001998376 also succeeded. This resolves the parent's pending run.

The initial scope checkpoint c92031f604e6a0d526bcf3e897dd8799371bfa17 had an
incorrect run/head/job attribution, corrected in the detailed checkpoint
note using freshly read run metadata and step results. Parent CI evidence
is never substituted for compilation of the new conditional source.

Preserve M06-scalar-full-ci.md, M06-scalar-stability-evidence.md,
M06-scalar-stability-review.md and their source/axiom/coverage JSON evidence.
The predecessor target run36113477726 and full CI36113477728 were already
recorded there; inherited failed checkpoints remain in history.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training conditional vector rates, native first-exit, later
independent carried-PBS re-solving and CarriedResolveStepBounds remain.
Preserve actual private seed/history laws, off-path cases and model-versus-
actual beliefs. Keep finite-T residuals when oracle error is zero and keep
the printed and corrected Theorem3 readings separate. M06 is NOT complete.
