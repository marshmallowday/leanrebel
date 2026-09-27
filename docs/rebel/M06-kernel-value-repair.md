# Changed-kernel compiler repair checkpoint

Starting source: dac8bd902ba368357d4a53f0d0b6b90a6d3dddeb, the latest observed
commit on rebel/m06-kernel-value-transport-checkpoint-20260927. Its branch head
was re-read through the GitHub plugin before branching. Main remains M05.
The repair branch is rebel/m06-kernel-value-repair-20260927; original branches
and accepted depth-native evidence are preserved.

## Observed failure and focused repair

The complete TARGET job log for 3ef56a217e22903aba945f1c3417e4810d468e73,
run 36292013486 / job 108543785041, was read through the GitHub plugin.
Declared-target compilation failed. The initial errors at core lines 51, 79
and 99 are `unexpected token 'recall'; expected '_' or identifier`.
Dependent fallback/parser errors follow. The lint/axiom step was skipped.
The uploaded failure artifact is 10922611596. Prior Python and source-snapshot
checks remain valid as their narrowly scoped historical observations, not as
Lean acceptance.

Rename the three perfect-recall binders to hrecall and update their uses.
No mathematical statement, assumption, coefficient, proof step, import, target,
control, dependency pin, workflow or auditor is weakened or removed. The
four generic lemmas retain exact full-kernel L1 discrepancy, fixed opposing
policies and arbitrary compatible old/new type domains. The depth integration
still uses the actual event-selected correlated seed/type law and retains
its native finite-T error and event probability denominator.

The owner ledger is updated with the same source commit; its full prior
version is retained byte-for-byte in M06-kernel-value-transport-coverage-at-dac8.json.
The independent accepted 51d5 global/full-CI evidence already present in dac8
is not rerun or used as acceptance of this repair.

## Next validation

Inspect the new exact-SHA target run first; repair any further actual compiler
or lint errors exposed by elaboration. Keep expected target/global audit counts
at 116/259 and inspect complete axiom records, including multiline output and
all named controls. Global and full-CI acceptance must be checked separately.
No Lean acceptance is claimed at this checkpoint. M06 remains incomplete.
