# d6c5 compiler failure and full-information index repair

Failed source d6c50c6607c5f449cdf7bbf1bc34cd09c5680443 is preserved on
`rebel/m06-primitive-support-20260927`. TARGET run 36286902665 / job 108529260920
failed at PBSCarriedSupport.lean:262:74. The complete finished job log was
obtained through the GitHub connector even while a previous job-summary query
still displayed compilation in progress. Artifact 10920609369 was downloaded
and its complete m06-targeted.log inspected.

Failure ZIP SHA-256:
e68280800eae1a98ff9d9f2c0b68869ca01b096d85058130cf8085bef9f6c250.
Failure log SHA-256:
ad69bea4e86af57cfbbfe13d5736aa0817aa42c73205a9ef37b8f58c4ad11187.

The native specialization supplied publicTrace M.toInfoSignals to a resolver
whose carried belief is indexed by publicTrace (fullInformation M).toInfoSignals.
These expressions retain different universe parameters; the dependent argument
state.belief could not typecheck. The diagnostic showed the original private
information universe up versus max (max ua uk) uq in the full-AOH instance.

The repair supplies the actual fullInformation M signal projection at that
argument, matching the native state and resolver. No cast or transport is added,
no universe is collapsed, no rate hypothesis is removed, and no conclusion,
control or sampling law is weakened. The correction is one expression plus a
line wrap in the native specialization's primitive-leakage premise. The generic
rate-budget math file is unchanged; it compiled in this failed target run, but
that alone is not final lint/axiom acceptance.

Old core blob: 8d1cbc364588b0df91e459d3ae4cdbceac2d777a.
Repaired core blob: 87d245e0e49df16c5a44b71a18fe34b4c47e2472.
Repaired core SHA-256:
35c902b492ae2c8c369fafdaae7aa37aee860bdbe6e2d01bf26a833b4a8c8393.

The repair is based on latest evidence checkpoint ae3443df4fced7e8169e3a20cfe1ec1d426a70e2,
which already records inherited 4784 global acceptance. Continue the checkpoint
branch after the repair, not the older failed source. Normal/slow lint and
transitive-axiom validation did not run after the failed target compilation.
The repaired source requires its own exact-SHA target/global/full-CI evidence.
All 134 arithmetic fixtures were already checked on exact d6c5; this single
Lean type-index correction does not retroactively make that source compile.
M06 remains incomplete.
