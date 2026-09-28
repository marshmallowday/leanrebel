# ce432689 finite-parent integration feedback and instance-scope repair

Candidate: `ce432689668ce58a0c8040820b7d06179582064f`.
All inspected runs have this exact head SHA and completed status.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36459218256](https://github.com/marshmallowday/leanrebel/actions/runs/36459218256) | 109053251997 | failure |
| ReBeL checks | [36459218063](https://github.com/marshmallowday/leanrebel/actions/runs/36459218063) | 109053247528 | failure |
| Targeted | [36459218039](https://github.com/marshmallowday/leanrebel/actions/runs/36459218039) | 109053246630 | failure |
| Inventory | [36459218193](https://github.com/marshmallowday/leanrebel/actions/runs/36459218193) | 109053246826 | success |

Complete decoded logs were fetched through the GitHub plugin. All three
compiler jobs report the same single diagnostic at
CFRDRecursiveSecurity.lean:134:0:

```text
automatically included section variable(s) unused in theorem
  GameTheory.ReBeL.cfrDRecursive_zero_prediction_allowance:
  [(who : Fin 2) -> Fintype (E.Action who)]
  [(who : Fin 2) -> DecidableEq ((fullInformation M).InfoState who)]
```

This is the unusedSectionVars linter promoted to an error by the unchanged
warning policy. The previous static review missed these automatically
included theorem arguments. No other source diagnostic was reported.
Absence of other diagnostics is not full module or downstream acceptance.

## Repair and review

Apply a scoped `omit ... in` for exactly the two reported instances immediately
before the zero-prediction allowance theorem. Both principal security theorems
retain their existing context. The zero-error proposition and its proof are
byte-for-byte unchanged; its redundant implicit instance parameters are
removed. No definition, solver behavior, numerical bound, mathematical
hypothesis needed by the proof, workflow, lint setting, heartbeat limit or
Python test is changed.

The actual cfrDInformationFallback definition is a pure legal policy lift and
does not require action enumeration or information-state decidable equality.
The average floor/finite-factor definitions and their structural constants were
re-read. Required finite-history/full-Choice instances remain in scope.
The arithmetic identity still has the independent finite factor/sqrt(t) plus
2*loss. The reduced/full models and explicit six universe levels are unchanged.

All new downstream consumers were re-read: the concrete zero-error invocation
supplies M/fallback/cut/remaining/bound/loss/t and no explicit instance argument,
so removing the redundant binders does not shift an explicit argument. The
two noisy-parent consumers retain their original finite History/Choice/InfoState
instances, parent cut1/remaining2 or cut2/remaining1, actual noise, reference
horizon3, stage/late clocks and aligned schedules. Empty budget examples use
local instances rather than generic section variables; no identical generic
unused-section pattern remains in this module. Parent security, budget
comparison and native execution expressions are unchanged.

Static checks confirm the only Lean edit is the scoped omit, no new declaration
names, library lines at most 100 columns, and no transport-source pattern.
This review is not a successful Lean compile. New-SHA Actions must still
compile every example/umbrella and finish all normal/slow lint and axioms.

## Partial checks and artifact evidence

checks static metrics LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0;
RATIONAL_RUNTIME_PASS. Checks ran 220 Python tests in 9.791s; inventory ran
220 tests in 8.984s. The full lint and axiom gates were not reached (no axiom
records). The new core and downstream modules are not accepted.

Artifact metadata was read; ZIP payloads were not read. Complete decoded logs
are the evidence. CI and the separate inventory run have no artifacts.

| Artifact | ID | SHA256 |
| --- | --- | --- |
| targeted | 10987058779 | dcca5ac24e4958a13afb7f68f3ee7f6d7490746eecf508b404c7271d1019e0d5 |
| global | 10987123905 | d9b15e04cbcbf87b80b8d4a37d53bb6dc73a747c5fae111ed54a9ab6036a59e9 |
| source | 10985929178 | 99e5f70c8ea314bf23e0fa3a5a412e5dd1445b8d3929787577c3b368e4980d62 |

Expected surface is unchanged: 183 build targets, 145 targeted/286 global
audit modules, 220 Python tests. The e590b4f accepted dependency remains the
last full acceptance; its result is not reused for this candidate.

Theorem 3's source interpretation is unchanged: the printed expression is
preserved separately, delta and finite T remain independent in the adopted
bound, child loss remains explicit, and useful small native-chain costs plus
rooted/original computation correspondence remain unproved. No source
obligation is promoted and M06 remains incomplete.
