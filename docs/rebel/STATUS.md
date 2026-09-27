# ReBeL status — native support baseline fully audited; schedule candidate pending

## Latest resumable checkpoint

Continue `rebel/m06-schedule-support-review-20260927`, the evidence and fixture
checkpoint directly above implementation 370384f660a3c57e8f08e98bcf40e3f7528020bb.
The source branch `rebel/m06-schedule-support-20260927` is preserved at 370384
so its in-progress validation is not cancelled by this review. The ancestor
chain includes 7944888ce60f11282d78b8b84b8be84fa9a3f540, latest initial checkpoint
f3cda937012b9c72e7e03b8aa6b7e9d9176f0093, native resolver source 3dfa and all
earlier M06 work. Main remains accepted M05, not the latest M06 source.

## Completed inherited validation

The exact 3dfa TARGET audit is accepted: 1,797 complete unique allowlisted
axiom records and 110 matching module lint passes. Its GLOBAL run 36281726986 /
job 108514756082 now also succeeded. Artifact 10920070597 was actually downloaded
and completely inspected: 4,962 complete unique allowlisted records, 253 module
lint passes, final global success, clean compiler diagnostics, static VERIFIED=1
and the exact-source rational-runtime pass. The full CI run 36281726988 /
job 108514874942 was separately checked and reports all gates successful.
M06-resolver-support-global-accepted.md and the owning coverage JSON record
hashes, exact scopes and historical pending observations. Do not repeat these
completed reviews or the earlier b833 global audit (4,939 records / 253 lints).

## New native finite-schedule slice

370384 adds the forward sum of actual full-state support charges, visit-count
and first-hit composition, native noisy depth-CFR specialization and the bounded
future sampling comparison. Three Lean controls separate hit probability,
visit count and stage-input/final-output boundaries. Every consumer includes
the new module; no old test, module, gate or dependency pin was removed.

Its exact TARGET run 36283825513 / job 108520661241 was still compiling the
declared M06 targets when checked. Normal/slow lint and transitive-axiom
validation were pending. Obtain its final artifact and inspect every complete
record before accepting the new source. Neither baseline success nor editing
files is validation of 370384. Full/global runs require separate checks.

Seven new Fraction fixtures are committed in this review. All 127 local tests
passed on the source snapshot plus the new code/consumer/fixture changes. The
fixtures independently enumerate paths and forward charges, including all
2,187 three-stage kernel/root combinations, the 7/16-versus-1/2 distinction,
empty/final-output boundaries, repeated bad states, stopped/missing events and
wrong private-model prefix weighting. They are not Lean proofs. Source and
fixture hashes are in M06-schedule-support-coverage.json.

The charge may overcount repeated defects and includes the last transition.
Small primitive leakage, changed-PBS native/late gaps and source-specific signed
CarriedResolveStepBounds remain open. Preserve joint compatibility, the same
unknown opponent, actual public-event denominators and finite-T residuals.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 is incomplete; learner convergence is not a substitute for test-time safety.
No background monitoring is implied.
