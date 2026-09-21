# M06 information-set child repair restart

The actual remote source at restart was a783fd1ed702088986b7279cbefe059fc4201cf8
on rebel/m06-pbs-information-20260921. The new working branch is
rebel/m06-information-repair-20260921, created from exactly that commit.
It includes the earlier local-history repair 7ec45dc4 and the reverse-policy,
original-PBS information-set CFR, and eight-control compiler candidates.
Do not reset to b0564668 or replay the superseded e92c740e repairs.
Main was read separately at 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
No force update, history rewrite, or main integration is performed.

## Exact observed failures

Target run 35554593950/job 106195648735 failed. Artifact 10619867996
contains two ill-typed dependent rewrite motives in PBSRootDecode and an
unsimplified Option.elim in the expectation theorem. The source archive is
artifact 10619777893 from run 35554593952, whose source marker is a783fd1e.
Archive SHA256: abadb7e022984a3d16dc07cf8079b2e0728561aca5fefc0f57b2153759d35715.
Full ReBeL run 35554593952/job 106195648938 failed its static architecture
step: TRANSPORT_ANALYSIS_SOURCE=4, expected zero. That audit and all existing
validation gates are to remain unchanged; repair the authored proofs instead.

## Next dependency-closed work

Use type-explicit nondependent option-law equalities for the local decoder,
complete the expectation reduction, and remove source-level transport tactics
by proving the same equations from explicit definitions and typed equalities.
Then validate the existing reverse-policy and original-PBS Nash transfer slice.
After it passes, connect its actual information-set child output to the
parent's conditional-value contracts without assuming child optimality.

This document is a restart checkpoint, not a proof acceptance. Preserve every
original coverage obligation, counterexample, positive error term, dependency
pin, and test. Independent recursive re-solving and its source-faithful
security correspondence remain separate original M06 obligations.
