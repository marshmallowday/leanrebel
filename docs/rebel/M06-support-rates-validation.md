# M06 support-rate continuation — validation checkpoints

## Starting point and branch choice

Work starts from the latest integration source
`7326f1e40011b1d4329f09e743491cc7bc7e5746`, not main or the older
public-event branch. The continuation branch is
`rebel/m06-support-rates-20260927`. It preserves the integration source and
both of its parent histories. A separate branch allows the still-running
integration-wide ReBeL audit to finish without the branch-local concurrency
cancellation caused by a new source push. No main update or force push is used.
All GitHub access, artifact downloads and repository writes use the GitHub
plugin. Local operations only inspect plugin-downloaded source/artifact bytes
and run non-Git checks; no local Git command or direct GitHub HTTP is used.

## Inspected exact-source target evidence

Source: `7326f1e40011b1d4329f09e743491cc7bc7e5746`.
Target workflow: 36275563682; job: 108497496370; artifact: 10916654865.
The job succeeded. The actual artifact was downloaded through the plugin and
its SHA-256 verified:
`2eb39d8abe4ed4291a8cdcebaf62ad1e36e798c9f44ebdc4180c6d540b37e63f`.
The extracted `m06-targeted.log` SHA-256 is
`38cff79000dba001308a1724e275bf6ed670f7fc1dc79d0958f62a8adaac8435`.

The log identifies the exact source above and Lean 4.33.1. It contains both
successful build completions (3,475 and 3,467 jobs), 110 module lint-pass
markers and `EXACT_LEAF_VALIDATION_PASS modules=110`. All 1,739 complete
`EXACT_LEAF_AXIOMS` records were parsed; every axiom set is contained in
`propext`, `Classical.choice`, `Quot.sound`. All six newly integrated tail and
example declarations occur in this actual output. No error/warning diagnostic
or failed target gate was found. These are combined-source results, not reused
parent results. They do not imply completion of M06 or Theorem 3.

## Exact source available for reproducible review

Source snapshot: ReBeL run 36275563642, artifact 10916773484.
Verified ZIP SHA-256:
`04f9f5b65db04b0e147767f136e02d9d09552996bfe9eca5e373c81c55a69838`.
`source-commit.txt` matches 7326f1e4. Verified tracked-source TAR SHA-256:
`ec6a4a5b3c19af78d53aa6e84b62d0ad678cc686d26a96890d1d5c5310d9a762`.
The archive contains no .git directory. It was extracted for source review,
not represented as a local Lean installation or a compiled result.

## Other baseline gates at this checkpoint

Full CI 36275563654 / 108497657992 reports success, but its actual detailed
logs have not yet been inspected here. Do not upgrade that metadata to
inspected compiler/architecture evidence. Global ReBeL run 36275563642 /
108497538005 is still running its compiler/lint/axiom stage; its final actual
artifact is pending. Source inventory evidence also remains to be inspected.

## Dependency-closed next slice

Derive support-failure rates from incoming unsupported mass and actual-visit
one-step kernel support leakage. Unlike full source-atom variation, this must
not charge an incoming distribution merely for having different positive
weights inside the same model support. Retain impossible observations, actual
unknown-opponent execution, arbitrary incoming laws, and finite horizons.
Connect the bound to the existing carriedBeliefUpdate failure event, add a
real budgeted-child consumer and hostile exact-rational controls, and retain
all existing target/global audit wiring. New Lean source is not yet committed
or compiler-validated at this checkpoint.

The full independently re-solved schedule, small quantitative leakage rates,
changed-PBS native/late gaps and CarriedResolveStepBounds remain separate
obligations. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. No learner convergence, support floor, or dropped finite-T term is
introduced to claim test-time safety.
