# ReBeL status — primitive support checkpoint; M06 incomplete

Continue `rebel/m06-primitive-support-checkpoint-20260927`, an evidence-only
descendant of source d6c50c6607c5f449cdf7bbf1bc34cd09c5680443. Leave implementation
branch `rebel/m06-primitive-support-20260927` at d6c5 while its checks run.
The chain retains 03d75bf and the original latest 2a7c55a checkpoint. Main is
accepted M05, not the latest M06 branch. No source or validation gate is changed
by this evidence commit.

## Current source and next check

TARGET 36286902665 / job 108529260920 was compiling the declared M06 targets
when inspected. Obtain its final complete artifact and inspect compiler,
normal/slow lint and every complete transitive-axiom record, including all new
names in M06-primitive-support-coverage.json. No new Lean acceptance is claimed.
GLOBAL 36286902680 / job 108529260867 independently passed static architecture,
widths, ledger/fixtures and runtime, and was in compiler/lint/axioms. FULL CI
36286902701 / job 108529261017 was separately in progress at the first check.
Check final results independently; older passes do not validate new code.

The exact d6c5 source snapshot artifact 10921090249 was downloaded through the
connector, source identity and blobs checked, then extracted without git.
All 134 Python tests plus ledger/inventory checks passed on that exact source.
This is independent arithmetic evidence, not local Lean compilation.

## Completed inherited acceptance

Do not repeat 4784's completed target/global inspections: target has 1,823
complete allowlisted records and 111 normal/slow module lints; global artifact
10920945334 has 4,988 complete unique allowed records and 254 module lints.
The complete global validation, frozen architecture and rational-runtime reports
were actually inspected. Full CI separately succeeded in job-step metadata.
M06-schedule-support-global-accepted.md and its owning coverage JSON record the
final result while retaining previous pending observations and failed candidates.
Inherited 3dfa and b833 acceptance is preserved too, not evidence for d6c5.

## Scope and remaining obligations

The new candidate derives native first-hit bounds from primitive good-state
support leakage. It excludes the final transition and avoids charging persistent
bad states repeatedly. Seven core definitions/theorems and five Lean controls
retain private model pairing, joint PBS compatibility and the same unknown
opponent. Seven new Fraction fixtures include 2,187 inhomogeneous schedule cases.

Small primitive rates for unrestricted finite-T CFR are still explicit unmet
obligations, not consequences of equilibrium quality. Changed-PBS native/late
signed value gaps and constructed CarriedResolveStepBounds remain open. Keep
actual public-event denominators, finite-T residuals and the R5 source distinction.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
M06 is incomplete. No learner-convergence premise or background monitoring
replaces test-time safety or exact-source validation.
