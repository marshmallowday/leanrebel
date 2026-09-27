# ReBeL status — carried-value joint-import repair pending CI; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927 from re-read HEAD
c975ad769a89e8baf627f2741d2f12974753cc51. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Connected login marshmallowday
and current admin/push permissions were rechecked through the GitHub plugin.

At c975ad7 the concrete example fuel repair passed and all declared M06
targets built. Joint imports now expose one new declaration name collision:
PBSCarriedValue and existing CFRDRefreshMix both define
GameTheory.ReBeL.carriedMemoryStep_selected_expect. CI 36312895797 and
ReBeL checks 36312895880 fail the umbrella build; target 36312895850 fails
the generated joint audit import. Full lint and transitive axioms remain
unverified. Complete job logs and artifact metadata were inspected.

Rename the new result to carriedMemoryStep_selected_late_expect and update its
caller/current documentation, preserving the old public declaration.
Theorem statements, proof bodies, workflows and audit gates are unchanged.
See M06-carried-value-c975ad7-failure.md for evidence and collision review.

Static architecture, 160 Python tests and the rational runtime passed in
ReBeL checks. Inventory 36312895889 also passed 160 tests.
The entire carried-value batch remains unaccepted pending the repaired SHA.

The full implementation and semantic boundaries remain in M06-carried-value-batch.md.
It combines chosen-model posterior identification, primitive rates, conditional
gap transport, same-private-draw late continuation, native forward signed loss,
CFR security connection, constructed step bounds, solver examples and controls.
Retain 156 build targets, 118 targeted/261 global audit modules and 160 tests.
The accepted fa95a3d results remain historical, not evidence for repaired source.

Historical coverage.json must stay at blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. Progress belongs in the M06 owner
ledger, with the previous complete state archived at the c975ad7 checkpoint.

The user's additional instruction prohibits subagents. All further work is by
the main agent. After this repair passes all required verification, implement
remaining related M06 tasks in large dependency-ordered batches, and consolidate
CI fixes. Do not insert a workflow wait after each small lemma or file.

After updating the branch, confirm distinct CI, ReBeL checks and M06 targeted
runs at that SHA; schedule this chat once for ref-update plus approximately
50 minutes in Asia/Tokyo and end. If still running at the next check, schedule
another single check about 20 minutes later. Do not stop running workflows.

Remaining: recursive type-kernel identification; useful solver-specific small
source/execution/support rates or stronger signed value envelopes; original
SEARCH-FRONTIER/SEARCH-CFRD/SEARCH-ERROR and corrected/restricted SAFE-THEOREM3
acceptance. Primitive rates are not consequences of Nash accuracy. M06 is incomplete.
