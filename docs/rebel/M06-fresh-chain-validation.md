# M06 finite fresh chain — exact-source validation and compiler loop

Proof source: `46126f37dbaa83a2f064f511e9617843d0ce308a`, preserved on
`rebel/m06-fresh-chain-20260924`.
Documentation/restart branch: `rebel/m06-fresh-chain-reviewed-20260924`.
This recording checkpoint changes FOUR DOCUMENTATION FILES ONLY. The proof
branch remains untouched so its independent ReBeL run is not cancelled by notes.
All remote access and checkpoints use the GitHub plugin. Main is not a write target.

## Accepted target-SHA build, lint and transitive axiom audit

M06 run35964794524/job107520892185: SUCCESS, completed
2026-09-24T06:42:27Z. All124 declared M06 targets compiled, including both new
CFRDFreshChain modules, their root-security consumer and every hostile control.
The completed supplemental proof-slice gate also succeeded; no skipped gate is
counted. Artifact10793738643 was downloaded through the GitHub plugin:

    m06-targeted-46126f37dbaa83a2f064f511e9617843d0ce308a
    sha256:429bb5b75a1a0992b23950703517f7a6edf6f1484edfbdffcdee42eeea2ef5f5

The archive digest matches the API. Its complete7954-line m06-targeted.log was
inspected, identifying this exact SHA and Lean4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The log records:

    EXACT_LEAF_MODULE_AXIOM_PASS ...CFRDFreshChain: declarations=17
    EXACT_LEAF_MODULE_AXIOM_PASS ...Examples.CFRDFreshChain: declarations=23
    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1291
    EXACT_LEAF_VALIDATION_PASS modules=86

All86 registered modules have their lint-pass and module-axiom-pass markers.
The transitive auditor covers public, private and generated declarations.
Only propext, Classical.choice and Quot.sound are allowed. In particular the
root security theorem, positive biased-parent control and changed-reference
negative control have explicit successful audit entries. No source error or
warning appears in this log. The pinned Batteries runner already selects slow
checks via getChecks(slow := true); no separate defLemma invocation is claimed.

## Whole-library CI and independent ReBeL status

Full CI35964794518/job107520892015: SUCCESS, completed
2026-09-24T06:46:33Z. This includes the whole public-library build, exact-source
and toolchain identification, inventory/compiler-resolved reuse signatures,
architecture Phases1/2/3 and reachability probes, library lint and tracked-file
cleanliness. Only the Windows-specific toolchain exposure was skipped on Ubuntu;
the actual build, audit, lint and cleanliness gates succeeded.
Inventory35964794526/job107520892133 and exact-source snapshot
35964794487/job107520978204 also succeeded at this exact source.

Independent ReBeL35964794487/job107520978527 was IN PROGRESS at recording.
Its line-width, static architecture, ledger/inventory/adversarial fixtures and
rational runtime with independently checked pure responses had passed.
Its all-ReBeL compile/lint/transitive-axiom step, started2026-09-24T06:33:01Z,
and final tracked-file cleanliness still need the final result. This pending
workflow is distinct from the completed target audit and full CI above.
Inspect that preserved exact-source run before starting the next implementation.

## Accepted common-reference composition predecessor

Source639e3962a2db297fb3f767459d7269769a7ea0d5 remains preserved on
`rebel/m06-fresh-drift-20260924`. Its target35962837942/job107514893323,
full35962837872/job107515074899 and independent ReBeL35962837863/
job107514896065 all succeeded. See M06-drift-composition-validation.md for
artifact evidence, the three accepted composition lemmas and corrected counts.
The actual source audit list was84, not the earlier prose's92. This successor
preserves all84 and adds exactly two; the M06 list preserves122 and adds two.
No target, whitelist, workflow, pin, warning gate or heartbeat limit was weakened.

## Initial chain344e429d and repaired compiler failure

Source344e429d8242c1eee79ad11908931a8e22217ffe FAILED M06
run35963799184/job107517833654. The full decoded job log was inspected.
All older modules compiled. The following concrete errors were repaired:

- Inside the recursive definition the fixed section model parameter was already
  bound. Passing M again shifted fallback into the wrong argument position.
  Recursive self-calls now use the already bound model; external calls pass M.
- Sided-addition helpers selected an unintended operand ordering. One generated
  expensive definitional equality and reached the unchanged200000-heartbeat
  limit. Explicit add_le_add with a reflexive operand resolves the ambiguity.
- Reference preservation and local-optimality mismatches were downstream of the
  malformed recurrence, not missing strategic assumptions.

The repair did not weaken any existing conclusion or remove a control. Its
new noisy-parent root-security consumer and concrete positive-bias control
are in the same two registered modules and passed at46126f37. The skipped
supplemental audit at344 is not accepted evidence.

## Semantic review and remaining original obligations

See M06-fresh-chain.md for exact declarations, assumptions and the source map.
The chain computes actual fresh children at one fixed cut/reference prefix,
then privately draws a legal plan of the final computed average. The original
history law and noisy-parent root security are derived with the entire bound:

    C_error * predictionError + C_time / sqrt(T)
      + oldChildLoss + finalChildLoss + sum(interSolveDrift).

Measured drift sums are not useful vanishing error rates. This is not native
per-iteration sampling or independent solving at later propagated PBSs. No
equality of modeled and actual unknown-opponent posteriors is assumed.
Useful source-level drift/support/first-exit rates and CarriedResolveStepBounds
remain open implementation/proof obligations. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 stay pending. Preserve accepted M05 evidence
and the printed/corrected Theorem3 distinction. No local Git operation was used;
Lean acceptance is from the exact-source fork CI, not static local checks.
