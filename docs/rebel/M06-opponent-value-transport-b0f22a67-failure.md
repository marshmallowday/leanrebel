# M06 changed-opponent candidate b0f22a67: failed validation and focused repair

Source: b0f22a67dba7d1adfb1e743cf2730da2d59b60f7, on
rebel/m06-kernel-value-repair-20260927. GitHub plugin reads at the follow-up
confirmed this is still the branch HEAD. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Connected login remains marshmallowday,
with repository admin and push permissions.

## Observed failures

All four runs finished with failure at the exact candidate SHA:

| Workflow | Run | Job | Failure |
| --- | --- | --- | --- |
| M06 targeted proof feedback | 36300697701 | 108567667974 | Lean elaboration |
| CI | 36300697693 | 108567667876 | Same Lean elaboration failure during build |
| ReBeL checks | 36300697766 | 108567668311 | Frozen coverage base blob mismatch |
| ReBeL source inventory | 36300697721 | 108567667950 | Same coverage mismatch |

Complete decoded job logs were fetched through the GitHub plugin.
The targeted and full-CI compiler report the same first error at
PBSKernelValueTransport.lean:214:33:

    Application type mismatch: add_le_add_left leftCost ?m.224
    has type
      old.responseExecutionCharge first second fuel left oldType + ?m.224 <=
        old.optimalResponseExecutionCharge fresh fallback fuel payoff first second oldType
          + ?m.224
    but is expected to have type
      (old.kernel oldType).law.atomVariation (fresh.kernel newType).law +
        old.responseExecutionCharge first second fuel left oldType <= ?m.216

The targeted lint/axiom step and full CI post-build audits were skipped.
ReBeL checks passed the static line-width check (LIBRARY_LINES_OVER_100=0)
and static architecture step, then stopped before Python fixtures, rational
runtime and the global compiler/lint/axiom audit. The inventory workflow's
provenance checks passed before the same ledger rejection. No new-source
compiler, Python-test, lint or axiom acceptance is claimed.

Artifacts (metadata inspected through the plugin):
- targeted compiler artifact 10926185342,
  digest sha256:b80ace1b68a2a5ac1c76478fc6c9b3cdff73a64dad9a4663375d3253b5e3bbae;
- global precompiler artifact 10926110427,
  digest sha256:c6f10b4cb71a33d5acee9825d3330e7517b1b9752c5424fc77aa670f367020a5;
- exact-source archive 10925660242,
  digest sha256:84c47019ccee5201a4b669de034d946c8d54ebd39f14157feea261afc293e871.
No artifact was produced for full CI or source inventory at this failed SHA.

## Repair and unchanged obligations

Replace BOTH occurrences of the misoriented addition lemma with
add_le_add le_rfl leftCost / add_le_add le_rfl rightCost. This explicitly
retains the root-discrepancy term on the left of each sum while increasing
only the response charge. No mathematical statement or bound changes.

The added prose note in docs/rebel/coverage.json changed its historical blob
from 2fc8cc9ad6607d61bfe397707fb96ac322fbb800 to
24f2078e711ea4912609924081e4ba060424501e. As documented by
coverage-updates/README.md and enforced by coverage_updates.py, the accepted
M05 journal pins the exact historical base. Restore the original blob exactly;
do not edit the journal pin, checker, statuses, or accepted evidence.
The M06 progress note remains in STATUS and its dedicated owning ledger.
The complete b0f22a67 owner ledger is preserved in
M06-kernel-value-transport-coverage-at-b0f22a67.json.

The existing workflows were re-read: CI runs on push; ReBeL checks on push
to main/rebel/**; targeted feedback on push to rebel/m06* with the relevant
Lean paths. This repair satisfies all three trigger conditions. Existing
154 target names, 116 targeted/259 global audit module sets, dependency pins,
workflows and all adversarial controls remain unchanged.

Next inspect the repair's exact-SHA runs independently, including downstream
modules that were blocked by the first compiler failure. Do not use the older
9457c198 acceptance as evidence for this repair. M06 and the original
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR, SAFE-THEOREM3 remain incomplete.
