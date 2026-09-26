# b833 global ReBeL validation — final output inspected

This closes the pending global-validation check on the inherited support-rate
implementation only. It does not validate the subsequent randomized resolver
candidate and does not close M06 or original paper Theorem 3.

## Exact source and output

Source: `b833d49b430ac44c433658f3cc72fd130ff0a87f`.
Run: https://github.com/marshmallowday/leanrebel/actions/runs/36277876590
Compiler/lint/axiom job: 108504099546. Both this job and source-snapshot job
108504099412 completed successfully. The final artifact was produced at
2026-09-26T23:40:08Z, after the previous checkpoint's in-progress observation.

The GitHub plugin downloaded artifact 10918521959,
`rebel-validation-b833d49b430ac44c433658f3cc72fd130ff0a87f`.
The actual archive SHA-256 agrees with GitHub's reported digest:
`551e996b9ae537a019ec6369db73beedda04cb442593f35a0583afd88818e10e`.
It contains rebel-validation.log, rebel-mathlib-roots.txt,
rebel-architecture.log and rebel-rational-runtime.json.
The validation log has 1,655,894 bytes and SHA-256
`0c4727733579cd0002067524a944eaddfce8ea00eaf9ecb58e98aaea9d7e9767`.
Its first line is the exact b833 source SHA.

## Actual inspection, not a summary-only inference

The complete log contains 4,939 REBEL_AXIOMS records and
`REBEL_AXIOM_AUDIT_PASS declarations=4939`. All 4,939 records were parsed,
including multiline axiom lists, and every set is a subset of
`[propext, Classical.choice, Quot.sound]`. The one-line-only parser would have
missed 565 wrapped records; those were included in the final inspection.
There are 253 matching REBEL_LINT_BEGIN / REBEL_LINT_PASS records and
`REBEL_VALIDATION_PASS modules=253`. No Lean error or warning diagnostic was
found in that log. In particular the one-step support, full-horizon unsupported
mass and carried-posterior support-rate declarations have actual allowlisted
transitive records, not just their signatures.

The architecture log has VERIFIED=1, TRANSPORT_ANALYSIS_SOURCE=0,
REBEL_NONDEFINITIONAL_TRANSPORT=0, SORRY_OR_ADMIT=0, CUSTOM_AXIOM=0,
BUILD_OUTPUT_COMMANDS=0 and all other frozen gates satisfied. The rational
runtime artifact identifies the same source and status pass: 85 histories,
rounds 0/1/2 and 1,024 enumerated pure policies per player. That finite runtime
cross-check is not the full semantic refinement or a recursive safety theorem.

Earlier b833 target/full-CI evidence and the failed f14 attempt remain in
M06-support-rates-b833-validation.md. No failed or pending record was silently
overwritten. Source artifact 10917737140 was also downloaded via the plugin;
its original proof declarations, controls, target/audit lists, frozen gates,
ledger and pins were compared with the new candidate source snapshot.

## New-candidate boundary

The separate resolver-support changes need their own exact-source compilation,
normal/slow lint and axiom evidence. In particular, the 63aa candidate failed
its unchanged static transport gate; that failure and its repair are recorded
in M06-resolver-support-validation.md. The successful b833 global run cannot
be used to classify later uncompiled declarations as verified.
