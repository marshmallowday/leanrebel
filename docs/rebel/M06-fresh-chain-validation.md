# M06 fresh chain — exact-source validation and compiler loop

Active branch: `rebel/m06-fresh-chain-20260924`. Read its current remote HEAD
and exact-source CI before resuming. All remote operations use the GitHub
plugin; main, dependency pins, workflow gates and existing controls are unchanged.

## Accepted common-reference composition

Source639e3962a2db297fb3f767459d7269769a7ea0d5 is preserved on
`rebel/m06-fresh-drift-20260924`. M06 run35962837942/job107514893323 completed
SUCCESS including every declared M06 target and the supplemental auditor.
Artifact10793590654 (m06-targeted-639e3962a2db297fb3f767459d7269769a7ea0d5)
was downloaded through the plugin and its entire log inspected. It identifies
the exact SHA and pinned Lean4.33.1 and records:

    EXACT_LEAF_MODULE_AXIOM_PASS ...CFRDFreshValueDrift: declarations=17
    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1251
    EXACT_LEAF_VALIDATION_PASS modules=84

The 84-module audit checks public/private/generated declarations transitively,
with only propext, Classical.choice and Quot.sound allowed. The unchanged
Batteries runner passed each named module. Do not repeat the earlier prose's
92-module or separate-defLemma-run claims: those were not the actual source
list or invocation. The two new chain modules raise the source list to86 and
M06 target list from122 to124, preserving all prior entries.

## Initial finite chain344e429d

Exact source344e429d8242c1eee79ad11908931a8e22217ffe FAILED M06
run35963799184/job107517833654. Its full decoded job log was inspected.
All old modules compiled. The chain failed at the following concrete points:

- Inside the recursive definition, fixed section parameters are already in
  scope. Passing M again shifted fallback into the wrong argument position.
  The recursive call must omit that automatically generalized section parameter;
  external applications continue to pass M normally.
- The selected sided-addition helpers generated the opposite operand ordering.
  One induced expensive definitional equality, reaching the unchanged200000
  heartbeat limit. Explicit two-sided add_le_add with a reflexive operand avoids
  both ambiguity and unnecessary unfolding.
- The reference and child-optimality mismatches were downstream of the malformed
  recursive definition, not missing strategic assumptions.

The current successor repairs these sites without changing any existing theorem
statement, dropping a test or increasing the heartbeat bound. The skipped
supplemental audit at344 is NOT accepted evidence. Run/job IDs here are those
returned by the actual commit check-runs endpoint; do not reuse an unverified ID.

## Root-security consumer in the successor

cfrDFreshChain_security connects the finite chain to the actual noisy
sampled-value CFR-D parent. Its opponent envelope is derived from the actual
last child, with no caller-supplied child quality or common-reference certificate.
It retains the full bound

    C_error * predictionError + C_time / sqrt(T)
      + oldChildLoss + finalChildLoss + sum(interSolveDrift).

The comparison equilibrium only names the root game's value; neither the
algorithm nor the child construction consumes that witness. Outer T is positive
and finite. The new concrete hidden-type root control uses nonzero bias1/8,
old child loss1/4 and two genuine refreshes with losses1/4 then1/8. Its unknown
opponent is arbitrary behavioral, and both drift terms remain present.

The successor still needs its OWN exact-source compiler, lint, public/private
axiom, full CI and independent ReBeL results. A source commit is not validation.
No locally executed Lean build is claimed; local checks are static only.

## Original obligations stay pending

This chain re-solves at one fixed original cut/reference prefix. The final draw
is the existing private legal-plan realization of the computed average, not an
invented native CFR-round draw. It does not establish independent re-solving at
later propagated PBSs or equality of model and actual unknown-opponent beliefs.
Measured drift sums are not useful vanishing drift rates. Source-level drift,
support/first-exit bounds and CarriedResolveStepBounds remain to be derived.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Keep all accepted M05 and printed/corrected Theorem3 distinctions.
