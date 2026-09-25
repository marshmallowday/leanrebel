# ReBeL status — M06 in progress; M05 accepted

## Current scalar-tail continuation

Work branch: `rebel/m06-scalar-tail-20260925`.
Read `M06-scalar-tail-validation.md`, `M06-scalar-stability-validation.md`,
`M06-scalar-stability-coverage.json` and `M06-scalar-stability-resume.md`.
The preceding accepted-slice STATUS remains in STATUS-before-scalar-stability.md.

Starting checkpoint2e1de273b9164743decdd8a283b3249f34bf5600 is preserved.
Initial candidate ce75519c49043af2b8a640efc82ffa6cfa7e3dca failed in the new
example; the main scalar stability module compiled. Repair
737704a90113d99ac135cbd6455ecf2bb7a563e3 changes proof tactics only and stays on
rebel/m06-scalar-stability-20260925 with its own CI. Failure run/job/artifact
and exact content hashes are recorded in the validation file.

The current extension derives a uniform late-output scalar bound using the
explicit half-tolerance iteration cutoff. Both solver outputs share one joint
PBS and the result is about reach-weighted averages, not individual iterates.
The existing budgeted/noisy-depth comparisons and sharp coupling counterexample
are retained. All83 Python tests pass locally. The current source still awaits
its own exact-SHA Lean compiler, lint and transitive-axiom results.

## Preserved evidence and trust boundary

Predecessor4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5 has SUCCESS in independent
ReBeL run36103763078/job107971751432, re-read via the GitHub plugin. It also
has the earlier recorded target/full-CI passes. Do not reuse that evidence as
validation of a new source. Main and all predecessor refs are unchanged.

No theorem, old target, test, workflow, dependency or axiom allowance was
weakened. The136 target list and98-module supplemental audit retain every old
entry. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. M06 is NOT complete. Native/late-training CONDITIONAL value rates,
first-exit rates, later independent carried-PBS re-solving and
CarriedResolveStepBounds remain. Preserve actual private seed/history laws,
off-path support, model-versus-actual beliefs, finite-T residuals at zero
oracle error and the printed/corrected Theorem3 distinction.
