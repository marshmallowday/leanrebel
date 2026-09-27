# Native finite-schedule support composition

Project dependency for ROADMAP M06, not an acceptance of paper Theorem 3.
Start from evidence checkpoint 7944888ce60f11282d78b8b84b8be84fa9a3f540,
which directly retains the latest f3c checkpoint and native implementation 3dfa.
Implementation branch: `rebel/m06-schedule-support-20260927`.

## Statements and semantic boundary

`GameTheory.Analysis.ReBeL.PBSCarriedSupport` adds one forward charge definition
and four comparison theorems. The generic layer uses existing native
`carriedMemoryStep` and `carriedResolvedSupportCharge`, not supplied transition
bounds. Write mu[k+1] = mu[k].bind(nativeStep[k]) and c[k] for the expectation
of the existing one-step charge under mu[k]. Then every stage exception
contained in unsupported-or-missing carried states has expected native visit
count at most mu[0](unsupported) + sum c[k]. The proof uses the already proved
native one-step output-support bound at each actual prefix. Consequently
first-hit probability is at most the minimum of one and that same quantity.

Complete state laws preserve history, selected private profile, current model
PBS and private-memory pairing. Arbitrarily correlated initial laws are allowed.
The unknown comparison opponent is fixed throughout, not changed between stages.
No model/actual posterior equality, independent resampling, or arbitrary product
of marginal type laws is introduced. The generic layer requires no finite
history carrier. The constructed depth-CFR specialization uses exactly its
existing finite-history/action assumptions, fallback, payoff, native noisy
stage parameters and actual resolver.

`pbsCarriedDepthFirstHitProbability_le_supportCharge` discharges event
containment for the actual noisy depth-limited CFR sampling exception.
`pbsCarriedDepth_support_future_error` feeds the bound into the existing
native-versus-history-first comparison for arbitrary bounded future kernels.
It requires a nonnegative absolute observation bound. This is a sampling-law
comparison, NOT a unilateral security, changed-PBS value or Nash bound.

The existing first-hit process inspects the INPUT to each scheduled stage.
It does not inspect the final output after the schedule. Our forward sum is
conservative: it includes the last transition charge as well and may count
multiple exceptional visits. Neither the sum nor its definition asserts that
primitive support leakage is small. Missing beliefs are charged conservatively
even though the narrower sampling exception excludes missing beliefs.

## Controls and consumers

The same module contains a quarter-leak finite-law control with three named
Lean checks: an empty schedule observes nothing, two stage inputs see hit
probability 1/4, and three inputs have first-hit probability 7/16 but visit
count 1/2. These reject treating visit mass as probability, observing only the
initial state, or counting the last output as an additional scheduled input.
All prior native-resolver controls remain unchanged and enabled.

The opt-in analysis root, declared M06 targets, and explicit normal/slow lint
and transitive-axiom consumer all include the new module. No existing module,
test, gate, allowlist, dependency pin or expected architecture count is removed
or relaxed. No new unsafe axiom, placeholder or native-decision trust is used.

## Validation checkpoint

Compiler, normal/slow lint, and complete transitive-axiom evidence for THIS
new source are PENDING. The exact implementation commit and workflow IDs must
be recorded after the push; source editing alone is not validation. The four
uploaded blobs match local byte-derived blob identities before the commit.
Local ledger/inventory checks and all inherited 120 Python fixtures passed
on the 3dfa source snapshot with these four code/consumer changes; this is
neither a Lean compiler run nor evidence for changed remote documentation.

The inherited 3dfa TARGET audit is separately complete (1797 complete records,
110 module lint passes); see M06-resolver-support-target-accepted.md. Its global
and full-CI checks have separate identities and do not validate this new module.

Next: inspect exact-source target output, repair compiler/linter failures
without weakening statements, add/inspect finite-law adversarial fixtures,
and record complete audit evidence. Primitive small leakage, changed-PBS
native/late value rates and source-specific signed CarriedResolveStepBounds
remain open. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending, preserving finite-T residuals and the paper/corrected R5 distinction.
M06 is incomplete. No background monitoring is implied.
