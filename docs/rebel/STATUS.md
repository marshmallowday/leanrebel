# ReBeL status — changed-opponent compiler/ledger repair pending CI; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927 from re-read HEAD
b0f22a67dba7d1adfb1e743cf2730da2d59b60f7. Main is unchanged at
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Connected GitHub login and repository
admin/push permissions were rechecked. No PR or merge is requested.

The b0f22a67 changed-opponent candidate failed all four exact-SHA runs:
TARGET 36300697701/job 108567667974 and full CI 36300697693/job 108567667876
reported a misoriented addition lemma at PBSKernelValueTransport.lean:214.
GLOBAL 36300697766/job 108567668311 and source inventory
36300697721/job 108567667950 stopped at the fixed coverage base-blob check.
Python fixtures and the new transitive axiom/lint audits were not reached.

This repair uses explicit add_le_add le_rfl at both response comparisons,
without changing their mathematical statements. It restores historical
coverage.json blob 2fc8cc9ad6607d61bfe397707fb96ac322fbb800 exactly, as required
by the accepted append-only M05 journal. M06 progress stays in its own ledger.
No checker, journal pin, workflow, dependency, target or control is weakened.
See M06-opponent-value-transport-b0f22a67-failure.md for logs/artifacts and repair
rationale. The complete previous owner ledger is preserved in
M06-kernel-value-transport-coverage-at-b0f22a67.json.

The candidate still transports conditional payoff, attained optimum and
signed gap under both compatible-kernel and opposing-policy changes, using
the two constructed optimal responses and retained own response. It connects
to the actual noisy depth-parent correlated query, with a separately solved
child control and four new independent Fraction tests. The old finite-T,
noise, child-loss and event-denominator terms remain explicit.
Read M06-opponent-value-transport.md for semantics and boundaries.

Earlier 9457c198 validation remains separately accepted (target 36293799005,
global 36293799056, CI 36293799070), not evidence for this repair.
Next inspect all repair runs at their exact SHA, including previously blocked
downstream modules. Require 154 build targets, 116 targeted/259 global audited
modules and complete allowed-axiom records, normal/slow lint and architecture
checks. After checking creation of the repair runs, schedule this chat once
for branch-ref update plus 50 minutes in Asia/Tokyo and end the response.

Remaining: actual recursive posterior identification; useful small root,
execution and primitive support rates; late-value composition and constructed
signed CarriedResolveStepBounds. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending. M06 is incomplete.
