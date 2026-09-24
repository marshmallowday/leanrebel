# M06 first-hit recovery and continuation

## Starting source and exact failures

Base: `160569f68d1c9d206a5f7002e2082a0679e5a152`.
Work branch: `rebel/m06-first-hit-recovery-20260924`.
All remote operations use the GitHub plugin; main is unchanged.

Targeted run35938303113/job107440275573 built the general first-hit induction
and its carried-depth connection. The last concrete example module failed at
line29 while elaborating `change`, reaching the default 200000 heartbeats.
ReBeL run35938303006/job107440275185 independently rejected the same source's
TRANSPORT_ANALYSIS_SOURCE=1 (expected0). Its line-width check passed.
Source inventory run35938302894 succeeded. These are failure diagnostics,
not full acceptance evidence.

## Repair checkpoint

Unfold just depthControlBelief, rewrite support_map, and provide the explicit
Fin4 witness0. This avoids reconstructing the dependent history type in a
transport expression. All original statements and concrete controls remain.
The default heartbeat limit, architecture budgets, imports, dependency pins,
normal/slow lint and three-axiom allowlist are unchanged.

Inspect this checkpoint's exact-SHA target, ReBeL, inventory and full-CI jobs.
Only successful inspected results can establish acceptance. The next work is
a source-dependent bound beyond the already implemented sampling comparison;
first-hit bounds alone do not discharge CarriedResolveStepBounds or Theorem3.

## Source/coverage boundary

This slice supports SEARCH-ERROR (supplementG/I) and SAFE-THEOREM3 (main§6,
supplementG), but those original rows stay pending. Preserve finite outerT,
positive prediction and child errors, unknown opponents, unsupported histories,
private-profile/model-PBS pairing, and the printed/corrected Theorem3 distinction.
No full-M06 completion, learned-network guarantee or numeric refinement is claimed.
