# M06 carried-value batch: ed2fad feedback and focused repair

Source: ed2fad241260b8df23d7e47448a817ca9458e464.
Branch: rebel/m06-kernel-value-repair-20260927.
The scheduled 2026-09-27 follow-up rechecked login marshmallowday, admin/push
permissions, work HEAD ed2fad and main
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No other work was overwritten.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36306984820](https://github.com/marshmallowday/leanrebel/actions/runs/36306984820) | 108585454998 | failed Lean build |
| ReBeL checks | [36306984802](https://github.com/marshmallowday/leanrebel/actions/runs/36306984802) | 108585454945 | failed static architecture |
| M06 targeted | [36306984787](https://github.com/marshmallowday/leanrebel/actions/runs/36306984787) | 108585454930 | failed target build |
| Source inventory | [36306984806](https://github.com/marshmallowday/leanrebel/actions/runs/36306984806) | 108585455401 | success, 160 Python tests |

Every run's head_sha matches ed2fad. Complete decoded job logs were fetched
through the plugin. The seven new Fraction tests passed in the source-inventory
job. Its log says Ran 160 tests and OK. These are not Lean proof acceptance.

Two independent blockers were found and repaired together:

1. PBSOpponentModelTransport.lean:457:17 reports unused simp argument
   Nat.zero_add. Follow the actual Lean diagnostic by removing that redundant
   argument, retaining executionKernelCharge, zeroKernel, bind_pure and zero_add.
   No linter option is disabled and the horizon-splitting statement is unchanged.

2. ReBeL's static phase2 audit reports TRANSPORT_ANALYSIS_SOURCE=1, expected 0.
   scripts/phase2-audit.ps1's existing source rule counts the change tactic.
   The new PBSCarriedValue.carriedMemoryStep_selected_expect used it to reduce
   storeCarriedDraw/resolvedNextState projections. Replace that step with
   explicit definitional simplification of those canonical definitions, then
   the same expectation/runner composition identities. No cast or transport is
   needed. Do not edit the audit, its pattern, budgets or workflow.

The build failure is upstream of the new PBSCarriedValue and its examples;
therefore their compilation, normal/slow lint and complete transitive-axiom
audits remain pending. CI post-build architecture and full-library lint did not
run. ReBeL diagnostics stopped before its Python/runtime/compiler checks.
Line-width check passed with LIBRARY_LINES_OVER_100=0.

Artifact metadata inspected:
- Target 10928305218: sha256 72c2944335ee3f3204eecf5e0ab5d6a69d8d4d1513f4480c0ef854333aa6611c.
- ReBeL diagnostic 10927352115: sha256 31e81f719ed42837a248550368d65605ad34ca876ea18d82ff2e45b2cda56527.
- Exact source 10928265011: sha256 75867a469055f8a0eb595ada7010897f56b16561de7eeb7407df7333f52a92c9.
- CI and inventory have no artifact. Binary archives were not downloaded.

This repair changes only the two proof scripts and their evidence records.
It retains 156 targets, 118 targeted/261 global audit modules, 160 Python
tests, all theorem statements, frozen coverage.json and the workflow triggers.
All new-source validation must be obtained from the repair commit's own runs.
No local/plugin Lean or Python execution is claimed. M06 remains incomplete.

The user now prohibits subagents; perform all future work in this chat's main
agent. Continue the user's large implementation batches after this batch's
repair and required validation pass. After a new branch update, confirm the
same-SHA runs and schedule a single current-chat follow-up about 50 minutes
later in Asia/Tokyo.
