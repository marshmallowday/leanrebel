# Exact-source 628b6212 feedback and third focused repair

Source: 628b6212a9c64189c99355a6aea46fcc0487b9d7 on
rebel/m06-kernel-value-repair-20260927. The source is not accepted: the targeted
compiler and independent static architecture gate each exposed an actual issue.
The branch head was re-read through the GitHub plugin before continuing.

## Targeted compilation

TARGET 36292939236 / job 108546359029 failed. The complete plugin-downloaded
artifact is 10922359582, ZIP SHA-256
4d3b057843b1b07761d51554f59035c92d5cb1ff81709323996fce864559bf99.
The 23,119-byte m06-targeted.log begins with the exact source above and has
SHA-256 40ce935678972fd814b895618445e57553e82a1e5536bee4ddf54a8ee518509e.

Both generic PBSKernelValueTransport and integration PBSDepthKernelGap now
BUILT under Lean 4.33.1. This is compilation evidence for their exact 628b6212
blobs only, not normal/slow lint, transitive axiom or complete-slice acceptance.
The example module failed at two proof steps. At line 53, case-splitting the
projection types.2 left the original conditional unchanged. At line 89,
unfolding kernelValueSlice in the same simp set as kernelValue_payoff_zero
prevented the intended payoff rewrite; the lower bound was not reduced to 2.
The target lint/axiom step was skipped.

Repair the observable bound by splitting its actual conditional, and rewrite
both explicit payoff values before simplifying the kernel projections. All
examples, their statements, the exact discrepancy 2 and actual noisy-parent
integration control are retained.

## Independent architecture failure

GLOBAL 36292939304 / job 108546413147 failed before Lean setup. Its complete
job log identifies TRANSPORT_ANALYSIS_SOURCE: expected 0, got 2. The two new
change tactics in the attained-maxima proof caused this measurement. No baseline
or audit script is adjusted. Ordinary dsimp only beta-reduces the two lambda
applications instead; no explicit type transport is needed for this proof.

Its plugin-downloaded artifact 10922897732 contains only the 1,780-byte
rebel-architecture.log, not a compiler/lint/axiom log. ZIP SHA-256:
e9a587bebfc187dceb75a1b813a5a34d477e3c46b768d5275cd9e5c4f67e20db.
Architecture log SHA-256:
b76966928b995c0fefd2192ed37f625cfa5c10e9f7609b003781b06a689c7187.
No gate is weakened, bypassed, relabeled as success or replaced by this review.

## Exact-source reconstruction and arithmetic checks

Source-snapshot job 108546413010 in GLOBAL 36292939304 succeeded. The plugin
downloaded artifact 10923435027; source-commit.txt matches 628b6212. ZIP SHA-256:
c37fe199fd07fff8f051d6ab2be143f518aaf58f0fc580d64af8786c0dda9be1.
The enclosed TAR SHA-256 was independently verified:
e3e0a78af1a663fe9ae6c4691feef9b25795b2fc6b3bebefee22d0e19250a501.
The core/integration bytes match the committed 028a1a3 and 528b8d5 blobs exactly.

On the extracted 628b6212 source, coverage and inventory structure checks passed
and python -W error -m unittest discover -s scripts/rebel/tests -v passed all
149 tests, including the eight changed-kernel fixtures. The test log SHA-256 is
2279d0764b9294e45b93bb4f0bd1ceaedbab81e4648874fd1ad1a0af3b264027.
Coverage/inventory log hashes are unchanged from the prior 6b7865 review.
These local checks invoke neither git nor direct GitHub access and are not Lean
acceptance. INVENTORY 36292939239 also succeeded.

FULL CI 36292939302 / job 108546412609 had no inspected final result; a new source
push may supersede it. The next exact source requires all target, global and
full-CI gates, including 116 targeted and 259 global module audits. M06 remains
incomplete and the four parent SEARCH/SAFE obligations remain pending.
