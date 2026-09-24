# M06 first-exit validation diagnostics

## Candidate 9165ff11

Exact source: `9165ff1155838c5427e2c53acfe7903a8a99975e`.
Target run35940857858/job107448326120 checked out that exact SHA and failed.
The inspected full log reports FinDistFirstHit.lean:287:29 and :287:42:
linarith sees an unreduced `(pure (some (suffix, state)).isSome).prob true`.
The associated unused-simp diagnostics at line286 are consequences of the
missing Option.isSome reduction. The first-exit distribution, projection,
witness-law invariance and signed-error identity had no reported errors.
Dependent PBS/example modules could not yet be accepted.

Commit9537c4f34df2b015f1b6fe8b23c82ca81da0262d adds Option.isSome to the explicit
simp set. It changes no theorem statement, event, kernel, test, validation option,
heartbeat or dependency pin. Its proof source still needs successful validation.

## Targeted workflow trigger

The Math-only repair did not start the M06 targeted job: its paths covered
GameTheory/ReBeL/** and GameTheory/Analysis/ReBeL/** but omitted the canonical
probability dependencies. The next checkpoint adds GameTheory/Math/Probability/**.
It retains every previous trigger, job, read-only permission, pinned action,
compiler/lint/axiom command, timeout and diagnostics-publication step.
Full ReBeL checks have no such path filter and remain independent.

Earlier status snapshots listed different pending job identifiers. For the
9165ff11 failure, the authoritative completed-job response and downloaded log
identify job107448326120, source9165ff11, run35940857858. Never use a pending
snapshot or a different source's passing result as acceptance for this candidate.

The source-specific recursive-security obligations remain pending; refer to
M06-first-exit.md and STATUS.md. The refined charge is a real-valued analysis
quantity depending on actual kernels and future observables, not an executable
learned estimate or a bound uniform over unknown opponents.
