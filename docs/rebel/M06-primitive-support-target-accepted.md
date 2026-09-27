# Primitive good-state support rates: exact target accepted

Source: 35d0bc04dcc12c3badad5a577f5218b5cc6d9a75, preserved on
rebel/m06-primitive-support-checkpoint-20260927. This evidence resumes the
latest documentation checkpoint 37a4f2c5cc20e285bca054e4a0c544232a218235;
it does not change Lean source or claim completion of M06.

Target run 36287339648 / job 108530477785 completed successfully. Artifact
10920709979 (m06-targeted-35d0bc04dcc12c3badad5a577f5218b5cc6d9a75) was actually
downloaded through the GitHub connector and its complete m06-targeted.log read.
ZIP SHA-256: acc531a3c3d6a43c3896adbdf09f79052d9e95f5c8d49d045d5348030f86af40.
Log SHA-256: 3704e5b865e3666153723a0c50f5ad5947c6345a4038256ba11635f7641c5429.
The log begins with the exact source SHA and Lean 4.33.1 / 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

All declared M06 targets compiled. All 111 explicit normal/slow lint consumers
passed, with the same module set as the per-module axiom audit. Every one of
1,853 complete, unique EXACT_LEAF_AXIOMS records was parsed across line wraps;
their only dependencies are propext, Classical.choice and Quot.sound. Their
count equals the sum of all 111 per-module declaration counts and the final
EXACT_LEAF_AXIOM_AUDIT_PASS count. No Lean warning/error was present.

The audit contains all seven new core definitions/theorems and all five
named proof controls listed in M06-primitive-support-coverage.json, including
sequenceFirstHitProbability_le_rateBudget and the native
pbsCarriedDepthFirstHitProbability_le_primitiveRate consumer. Both edited source
blobs match the exact 35d0 source snapshot recorded at the preceding checkpoint.
The mathematical scope and explicit leakage premises remain those reviewed in
M06-primitive-support.md; these are not unconditional smallness or security claims.

This supersedes the prior TARGET pending observation only. Global run
36287339585 / job 108530593276 and full CI 36287339593 / job 108530515400
must still be checked independently; no new global artifact has been accepted
here. The existing 4784/3dfa/b833 acceptances and all failure history remain intact.

The next implementation slice is the conditional native-draw value gap of the
actual NOISY DEPTH-LIMITED parent, not just the ordinary full-game CFR solver.
It must retain the computed depth/noise/child/finite-T allowance and distinguish
actual event selection from changing conditional PBS kernels or opponents.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
