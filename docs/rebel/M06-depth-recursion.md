# M06 depth-sampling continuation checkpoint

## Resume source

Continue from the actual remote HEAD of `rebel/m06-depth-recursion-20260924`.
This branch starts at `993635f35761b5bca336a72b8ba74d85ae6b2186`, preserving
all carried-sampling and rooted-depth implementations. Do not restart from
`6c541fca`, `4bf56ccc`, or the older style-lint repair.

The GitHub plugin created this continuation branch and updated
`PBSCarriedDepthSampling.lean` in commit
`54ce64d53c578c05c1a3415d47ff3b8e5ade40d5`. The update only wraps three
101-character expressions; it does not change definitions, theorem statements,
proof arguments, dependencies, or validation settings. Read that exact source's
Actions results before asserting acceptance. Main is not a write target.

## Evidence recovered from the repository

The predecessor's targeted job `107420379142`, run `35931852591`, reports
success. The full ReBeL job `107434978711`, run `35936622300`, fails before
compilation on exactly three 101-character lines in the finite depth-schedule
expressions. These are the three lines repaired in `54ce64d5`.

## Next implementation work

Add concrete noisy depth-sampling controls with finite, distinct iteration
counts and execution/search horizons. Cover supported and unsupported actual
histories, retained profile/PBS correlation, missing beliefs, stopped stages,
and the existing finite recursive runner. Keep new declarations in the
analytic root, M06 target list, and normal/slow lint plus transitive-axiom audit.

Investigate a first-exception probability bound for complete schedules rather
than charging repeated exceptional visits independently. Any such bound must
be derived from native forward laws and preserve full private state.

## Unchanged acceptance boundary

Neither the existing finite-schedule comparison nor a sharper sampling-error
estimate is a recursive security theorem. The deepest child backend still
uses full-root CFR. Arbitrary-depth child solving, source-dependent model-value
drift, source-derived support-defect rates, and `CarriedResolveStepBounds` remain
separate obligations. Preserve finite outer T, nonzero prediction/child errors,
zero-reach completion, and the printed/corrected Theorem 3 distinction.

`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, and `SAFE-THEOREM3` remain
pending. No unrestricted M06 completion or executable numeric-refinement claim.
