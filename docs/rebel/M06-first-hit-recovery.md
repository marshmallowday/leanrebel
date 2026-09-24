# M06 first-hit recovery and continuation

## Starting source and exact failures

Base: `160569f68d1c9d206a5f7002e2082a0679e5a152`.
Recovery branch: `rebel/m06-first-hit-recovery-20260924`.
All remote operations use the GitHub plugin; main is unchanged.

Targeted run35938303113/job107440275573 built the general first-hit induction
and its carried-depth connection. The last concrete example module failed at
line29 while elaborating change, reaching the default200000 heartbeats.
ReBeL run35938303006/job107440275185 independently rejected the same source's
TRANSPORT_ANALYSIS_SOURCE=1 (expected0). Its line-width check passed.
Source inventory run35938302894 succeeded. These were failure diagnostics,
not full acceptance evidence.

## Accepted repair checkpoint

Exact repair: `01245b31164eabcb7012e98b36d57b470496dd8e`.
Unfold just depthControlBelief, rewrite support_map, and provide the explicit
Fin4 witness0. This avoids reconstructing the dependent history type in a
transport expression. All original statements and concrete controls remain.
The default heartbeat limit, architecture budgets, imports, dependency pins,
existing lint and three-axiom allowlist are unchanged.

Inspected successful workflows at this exact source:

| Workflow | Evidence |
| --- | --- |
| M06 target | run35939097445/job107442786882; compiler and supplemental audit passed. |
| ReBeL | run35939097447/job107442786889; complete compiler/lint/transitive-axiom and cleanliness steps passed. |
| Repository CI | run35939097488; success. |
| Inventory | run35939097484; success. |

The completed ReBeL result supersedes earlier pending snapshots. The next
first-exit implementation is a distinct source and needs its own validation;
this recovery's passing jobs must not be reused to accept the extension.

## Source/coverage boundary

This slice supports SEARCH-ERROR (supplementG/I) and SAFE-THEOREM3 (main section6,
supplementG), but those original rows remain pending. Preserve finite outer T,
positive prediction and child errors, unknown opponents, unsupported histories,
private-profile/model-PBS pairing, and the printed/corrected Theorem3 distinction.
No full-M06 completion, learned-network guarantee or numeric refinement is claimed.

The current continuation and exact-source CI state are recorded in STATUS.md
on `rebel/m06-first-exit-review-20260924`. Do not repeat the repaired support proof.
