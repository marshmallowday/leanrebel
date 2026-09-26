# M06 public-observation posterior bridge

## Starting checkpoint and scope

Continue on `rebel/m06-conditioned-query-20260925` from
`543849ea0fc3df25c95629d957561936ee16527a`, not main. Branch enumeration,
the latest repository-wide push workflows (which have no branch filter), the
source artifact's recorded SHA, STATUS and a fresh branch-ref read agree on
that starting checkpoint. Planning commit:
`af2b4da1776e97ee70c437c886fc80f8a633fae8`.
The source artifact 10896456006 has SHA256
38b5471a57e581fb2e1000ed3de7c479ca49ac44fe53463e8440e1ae235a98e1.
Main remains accepted M05. M06 and Theorem 3 are incomplete.

This is a project-level refinement of ROADMAP M06's public-carried-query
identification boundary, not acceptance of paper Theorem 3.

## Source and exact claims

FinDistSelection.lean now proves possible_preimage_iff and map_condOn_preimage
using only the existing public finite-support API. A projected event is possible
exactly when its preimage intersects actual support. Conditioning that preimage
and then projecting is the same law as conditioning the original projection.
The proof needs no finite carrier, independence, injectivity, minimum atom mass,
or PMF representation access. The event's preimage restriction is essential.

PBSConditionedNativeGap.lean extends the existing actual retained-iteration
execution, without defining a parallel runner or solver:

- pbsInformationCFRPublicEvent reads only the resulting canonical public trace.
- pbsInformationCFR_public_possible_iff identifies the real event's witness
  with PublicBelief.Possible for the computed-average execution.
- pbsInformationCFR_public_event_mass identifies the actual selection mass
  with that execution's public-observation atom probability, including zero.
- pbsInformationCFR_public_posterior_history identifies the selected HISTORY
  marginal with PublicBelief.condition, retaining the entire joint history law.
- pbsInformationCFR_public_native_mean_abs_le gives the existing finite-T native
  error divided by the actual public-observation probability.

The last bound still measures its gap at the ORIGINAL compatible full joint
TYPE kernels against the SAME computed average comparison opponent. It does
not evaluate a new gap at the selected posterior's changed kernels. The
execution opponents are arbitrary fixed legal policies and need not equal that
comparison opponent. Training and execution horizons may differ.

## Controls

The existing Examples.PBSConditionedNativeGap module now includes
pbsPublicPosterior_live: the genuine HiddenTypes full-AOH two-iterate solver
runs one canonical continuation step against arbitrary fixed legal opponents.
A supported public observation is constructed from an actual execution point,
and its selected history is exactly the canonical averaged-execution PBS.
No input posterior or equality certificate is assumed.

A separate finite-law control uses the existing independent uniform seed/type
and nonconstant output kernel. It selects output zero, derives event mass 1/2,
and proves that the selected output marginal is pure zero while the original
output is uniform. This tests a many-to-one projection; it is not an asserted
solver-generated payoff or regret table. hidden_selection_not_public proves
that selecting a hidden bit cannot be ANY preimage of a constant public
observation. absent_output_has_no_posterior rejects a zero-mass observation.
The inherited diagonal-correlation and rare-event controls are unchanged.

## Validation state at the source checkpoint

All additions extend the three already-imported and already-audited modules;
no umbrella, target list, auditor, workflow, dependency pin, lint setting or
architecture expected count changes. The supplemental gate still visits all
107 configured modules and global discovery still visits 251 modules.

Five new exact rational/wiring Python tests plus all prior tests passed:
97 tests, warnings treated as errors. Local log SHA256:
3ecabde353b91c9c668e1007c845894e84286bdda71aa7f154f3afd5440e3a58.
Coverage/inventory structure checks retain all 3,054 items and original statuses.
Prepared Lean source bytes match the plugin-created blobs:
FinDistSelection 89c66c699c5d2464e5d965e12bee276348eec0a6;
PBSConditionedNativeGap 939f440368cec193413f9f80f0104b058fbe1e72;
Examples.PBSConditionedNativeGap c651d1d7222e42608ea58a89acf0230407afef04.
These checks are not Lean execution. New-source compiler, normal/slow lint,
transitive axioms, all-ReBeL and full CI are PENDING the source push.
The prior repair's exact-SHA evidence remains in M06-conditioned-query-repair.md.

## Remaining semantic boundary

This identifies a fixed-profile PUBLIC posterior, not a fresh independently
re-solved carried PBS or independent posterior tags. Changing-opponent/PBS
rates, quantitative first-exit/support/event rates, recursive re-solving safety
and CarriedResolveStepBounds remain open. No source ledger row is promoted:
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No event-mass floor, exposed seed, discarded finite-T residual or learner
convergence premise is introduced. M07 is not started.

GitHub access and commits use the GitHub plugin; offline snapshot inspection
and rational tests use no local Git operations or direct GitHub HTTP.
