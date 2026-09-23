# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-depth-sampling-20260924`.
The branch preserves the rooted-depth implementation at
`964f6d639236d11addf44b79b3dee3fc2ef5d67b` and the earlier carried-iteration
checkpoints. Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Verified predecessor, do not repeat

The rooted-depth source 964f6d639236d11addf44b79b3dee3fc2ef5d67b passed
M06 targeted run 35888559368/job 107274927401, including target compilation
and the supplemental lint/axiom audit. ReBeL run 35888559003 and source
inventory 35888559143 report success. This supersedes the old pending
wording in M06-rooted-depth.md; no theorem or verification gate was weakened.

PBSRootDepthCFR computes the actual sampled-value noisy depth-limited parent
at a joint-PBS chance root. PBSInformationDepthCFR transfers all-deviation
Nash and actual-iteration laws to original local strategies. PBSCarriedDepth
uses that same iteration family at each incoming carried model PBS, keeping
the chosen profile paired with its own model posterior. The old full-state
finite-schedule comparison in PBSCarriedRecursion is also preserved.

## Current slice and validation state

PBSCarriedDepthSampling extends the depth-limited mixture identity to each
supported original history and to arbitrary reweightings within support.
An explicit actual unsupported-history probability bounds the discrepancy
without assuming support domination. Its history-first full-state comparison
retains the native conditional private profile/PBS pairing through arbitrary
subsequent finite kernels; it is not a public averaged-PBS reset.

The generic supported-history separation lemma was checkpointed at
ad086949b477e3f0ba6a01601cf7488853c841a4. The new depth-sampling module is in
the analytic root, M06 targets, and supplemental normal/slow lint and axiom
audit. Read this branch's exact-SHA Actions results; new-slice acceptance
is pending. Concrete depth-sampling controls and the finite-schedule
connection are the next implementation steps. See M06-depth-sampling.md.

## Remaining original obligations

Arbitrary-depth recursive child solving remains unconnected: deepest children
still use full-root CFR. Derive source-dependent model-value drift and
exceptional-mass rates instead of assuming model/actual posterior equality
or a vanishing support defect. CarriedResolveStepBounds remains a separate
undischarged safety obligation. Preserve finite outer T, positive prediction
and child errors, zero-reach completion and printed/corrected Theorem 3.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
No full-M06, unrestricted Theorem 3 or executable numeric-refinement claim.
M06-carried-iterations.md, M06-recursive-sampling.md and M06-rooted-depth.md
retain the preceding implementation history and evidence; M05 acceptance
and all earlier source qualifications remain unchanged.
