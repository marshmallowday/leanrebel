# M06 executed opponent/model transport

## Resume and scope

Starting checkpoint: `b8be33668cce9b9238692bc86da545a89d2bad5d` on
`rebel/m06-conditioned-query-20260925`. Its repository-wide push workflows
and a fresh branch-ref read agree with STATUS; main remains accepted M05.
The previous public-posterior source `5df5e6a049c9550bcc944c3ca8599a3b215605e7`
is already validated. Do not redo or weaken that proof.

This slice addresses the explicit remaining distinction between the stored
model continuation `chosen` and actual continuation
`Profile.update unknown who (chosen who)`. It will derive an outcome-law
transport charge from the actual incoming law and the one-step canonical
execution kernels. It will NOT identify the unknown opponent's posterior
with the stored model posterior.

## Dependency-closed implementation target

1. Extend the existing finite-law atomVariation API with kernel contraction,
   kernel perturbation and lost-support probability bounds, using the public
   FinDist probability/expectation interface, not a parallel probability type.
2. Derive finite-horizon canonical continuation variation from initial law
   mismatch and accumulated one-step kernel differences along ACTUAL visits.
   Preserve the incoming-law mismatch even at zero fuel.
3. Apply this charge to the actual carriedBeliefUpdate support failure and
   to mean public conditional transport, preserving impossible observations.
4. Add a genuine solver-facing consumer, positive and negative finite-law
   controls, and exact rational tests. Wire all new modules into the existing
   umbrella, targeted build and transitive-axiom/lint consumers.

The source charge is computed from real kernels; it is not an assumed final
safety inequality. Smallness of the charge under independently recomputed
opponents is a separate obligation and is not implied by child Nash or a
larger CFR iteration budget. Actual starting laws may differ from the stored
joint PBS, including a point-mass actual history.

## Validation and trust boundary

At this planning checkpoint no new Lean theorem is claimed or accepted.
Use the unchanged pinned Lean 4.33.1 and dependency manifest. No placeholders,
custom axioms, hidden seed disclosure, positive event-mass floor, discarded
finite-T error, lint suppression or architecture-count changes are permitted.
All GitHub access and checkpoint commits use the GitHub plugin; offline
snapshot inspection/tests must use no local Git commands or GitHub HTTP.

The exact source build, normal/slow lint, transitive axioms, original coverage
and inventory checks, adversarial tests, full ReBeL checks and full CI must be
reviewed at the implemented SHA before recording validation. Pending runs
must be left with exact SHA/run IDs for resumption, not called successful.

M06 and Theorem 3 remain incomplete. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 retain their original statuses. This slice
neither starts M07 nor discharges CarriedResolveStepBounds, full recursive
re-solving safety, changed-PBS native value rates, or a vanishing first-exit
rate merely by defining a computable charge.
