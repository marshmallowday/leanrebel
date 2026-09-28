# Query-cost batch accepted at 799b190

Exact source: `799b190595ca6c17893290a8b77ff5fdd056ee22`.
Branch: `rebel/m06-kernel-value-repair-20260927`.
The fb27d899/799b190 proof-repair loop is complete. This accepts this
dependency batch only, not M06 or SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3.
No earlier successful SHA was substituted for these results.

## Exact-SHA Actions and complete logs

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36494277547](https://github.com/marshmallowday/leanrebel/actions/runs/36494277547) | 109170057268 | success |
| ReBeL checks | [36494277633](https://github.com/marshmallowday/leanrebel/actions/runs/36494277633) | 109170057761 | success |
| Targeted proof | [36494277546](https://github.com/marshmallowday/leanrebel/actions/runs/36494277546) | 109170057195 | success |
| Source inventory | [36494277647](https://github.com/marshmallowday/leanrebel/actions/runs/36494277647) | 109170057745 | success |

Source snapshot job 109170057759 also succeeded. All four run head_sha
fields match the exact source above. Checks completed at 2026-09-28
23:25:14 UTC. Full decoded job logs, rather than only workflow conclusions
or clipped annotations, supplied the following evidence:

- 2410 unique targeted and 5544 unique global transitive axiom records;
  every dependency belongs to propext, Classical.choice, Quot.sound.
- All 152 targeted and 292 global registered modules have lint-pass
  records and final validation markers. The sets were compared with
  MODULES and the full source tree's proof_modules selection, without
  missing or extra modules. Audits include normal and slow lint.
- Full build 4319, lint build 4089, GameTheory.LintAll success.
- All three architecture checks VERIFIED; LIBRARY_LINES_OVER_100=0 and
  TRANSPORT_ANALYSIS_SOURCE=0. RATIONAL_RUNTIME_PASS.
- 230 Python tests: checks 10.413s and inventory 10.730s.
- The previously failing Option.isSome proof, all security consumers,
  concrete examples, umbrella, full lint and complete axiom audits passed.

These are GitHub Actions executions. No local/plugin Lean, lint, axiom or
Python test execution is claimed.

## Artifact metadata

| Artifact | ID | Bytes | SHA256 |
| --- | --- | --- | --- |
| CI audits | 11003411288 | 6206 | c725859c129be3f244b8dffe56b4953cf870a41f15ac6de0e1f6c49f5e6a4ce2 |
| Global validation | 11003499951 | 138382 | 47b0aa34c537085f8debbe3842d3a9096a8966f0829df971a6b959409f29474d |
| Targeted validation | 11003396957 | 55888 | 351d648a8bb629490867d17f481894b31065309ead6cea66c05a7b25a397a8de |
| Source snapshot | 11001979186 | 2931209 | 9457d9e026974463c2d20fdc2b95c0a9dff5bae1b3cb53ef24c1df406130d36c |

Metadata was read; ZIP contents were not. Inventory has no artifact.
Complete decoded logs are the proof/diagnostic evidence.

## Meaning accepted and remaining

The actual resolver is a no-op off fresh queries (stopped or absent PBS).
Interval diameter times actual query visits covers unsupported queries too.
Visits are an expected count, not a union probability, and need not shrink
with T. The finite noisy sampled parent supplies initial security; its
prediction error, finite-iteration term and twice child loss remain distinct.
The min cap chooses between two complete-chain bounds on the same native law.

The future law retains private profile/PBS/history correlation and one
draw through stage plus late play. No factual/model posterior identity,
prior reset or Nash-to-policy-closeness conclusion is made. General small
recursive rates and internal-rooted/fresh-original solver correspondence
remain open. See M06-query-cost-batch.md and M06-theorem3-interpretation.md.
