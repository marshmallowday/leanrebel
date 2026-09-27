# ReBeL status — primitive support type-index repair; M06 incomplete

Continue `rebel/m06-primitive-support-checkpoint-20260927`, now containing the
single-expression native resolver type-index repair above evidence checkpoint
ae3443df4fced7e8169e3a20cfe1ec1d426a70e2. All d6c5 code and inherited 4784
acceptance remain in its ancestry. Main is accepted M05, not latest M06.
The original source branch `rebel/m06-primitive-support-20260927` remains at
failed d6c50c6607c5f449cdf7bbf1bc34cd09c5680443 for reproducible diagnostics.

## Compiler failure and precise repair

The complete d6c5 TARGET log from run 36286902665 / job 108529260920 and
artifact 10920609369 establishes failure at PBSCarriedSupport.lean:262:74.
A prior job summary still displayed compilation in progress. The native factory
uses fullInformation M; its dependent carried belief cannot be indexed by the
original M's different publicTrace universe instantiation. The repair uses
(fullInformation M).toInfoSignals at that argument, without a cast, a universe
restriction or any weakened premise or conclusion. The generic math file and
all five Lean controls are unchanged. See M06-primitive-support-d6c5-failure.md.

Next inspect this repaired commit's own target compiler feedback, then all
normal/slow lint and complete axiom records, and global/full CI independently.
The failed source's target lint/axiom step never ran. Both edited modules remain
in the existing 111-module target and 254-module global audit consumers; no
workflow, gate, dependency pin, allowlist or control was relaxed.

All 134 Python fixtures and ledger/inventory checks passed on the exact d6c5
snapshot downloaded through the connector. That arithmetic evidence is not
Lean verification, and the repaired source needs its own compiler evidence.

## Completed inherited acceptance

Do not repeat 4784 target/global audit work: 1,823 target records / 111 lints;
4,988 complete unique global records / 254 lints, all allowlisted. Its full
static, runtime and global validation artifacts were inspected. Full CI passed
separately in job-step metadata. The owning schedule coverage and
M06-schedule-support-global-accepted.md record the exact results. Prior 370384/e1
failures and 3dfa/b833 acceptance remain preserved, not evidence for newer code.

## Proof scope and remaining work

The candidate derives first-hit probability rates only from good-state primitive
leakage and omits the last transition. It preserves actual full-state laws,
private model pairing and the same unknown opponent. Primitive smallness for
unrestricted finite-T CFR, changed-PBS native/late signed value gaps and
constructed CarriedResolveStepBounds remain open. Preserve joint compatibility,
actual public-event denominators, finite-T residuals and the R5 distinction.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
M06 is incomplete. No learner-convergence assumption substitutes for safety.
