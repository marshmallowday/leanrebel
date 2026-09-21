# ReBeL status — M06 in progress; M05 accepted

## Active sampled-continuation construction checkpoint

Continue on rebel/m06-sampling-resume-20260921; read its remote HEAD and CI.
This branch starts at c4fee1dbb01520be898fce5a888c6edcf6a43228, preserving the
latest actual information-set child sampling candidate rather than replaying
old decoder or line-width repairs. The inherited verified-contract checkpoint
is af6f600727b0c50906155c54f23a26e7529426fd and its proof source is
6416eebd9a67645fe94100db744cd4d049d17684. See the preserved prior STATUS in
M06-status-before-sampled-continuation.md for its evidence and scope.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098; no integration or force update.

## Saved stages and validation boundary

The inherited c4fee1db target run 35563438176/job 106220531451 failed at
PBSInformationSampling.lean:120 because Option.some_injective needs an explicit
type argument. Commit 9d356e4f0b3dba418da0f65595a8bb19341ec555 supplies E.History
without changing the theorem. Commit ade8175f24b5705de3072ae1f30556a4eaf42654
adds the carried-state construction. The following registration checkpoint
adds both modules to the umbrella and supplemental lint/axiom consumers and
adds the carried module to the existing target list. No prior target is removed.
The new source is a compiler candidate until its exact-SHA checks pass.

## Constructed dependency slice

PBSInformationSampling uses the actual decoded CFR iteration family and the
same uniform private iteration law as its own-reach average. It quantifies over
arbitrary fixed behavioral opponents while retaining the supplied joint root PBS.
PBSInformationCarried reuses PrivateIterationState to retain the selected child
iteration and actual history across a finite list of segments, refreshing an
optional model posterior from that selected full profile at each elapsed time.
The candidate segment-composition theorem preserves the entire joint state.
Its projected history law is the actual averaged child's continuation law.
Zero-length segments and impossible model observations are not discarded.

## Remaining obligations

Inspect the exact-source compiler, normal/slow lint and transitive-axiom output;
add nontrivial live and boundary controls before accepting this slice.
Then connect the sampled child execution to the parent's counterfactual/value
family and independent recursive re-solving. Segmenting one fixed child is NOT
independent re-solving at a new PBS, and the supplied/model PBS is NOT the
unknown opponent's true posterior. No individual sampled-iterate safety is claimed.
Preserve all existing counterexamples, positive prediction/child errors, outer
finite-T residuals and the distinction between printed and corrected Theorem 3.
Original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No M06 or complete-framework acceptance is claimed.
