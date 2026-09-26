# ReBeL status — public-event tail validation; M06 incomplete

## Current branch and checkpoint

Continue `rebel/m06-public-event-rates-20260927`.
Source checkpoint: `c87c70d7b1c6dce3d3699d2908eea72811d8e713`.
The current follow-up changes one deprecated simplifier name and adds four
exact rational boundary tests. Main source blob is
`c97f2c1ebe3fe079a3603d1d01d5ef864fa31cd5`; example source remains
`5d3d3572bc110241c7dfc1513e5fbbb85d99c663`.
M06 and Theorem 3 are NOT complete; main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

Base was the newest concurrent source `a76f1f32403f3cc1834d8f39d11b9802626ee592`
on `rebel/m06-conditioned-query-20260925`. A fresh ref read detected its
advance from 6bc0676 before any write; that newer change is preserved. The
isolated branch prevents overwriting parallel work. Planning checkpoint is
`65a1612311836767d6a27c1ce47de82e1611cd46`. No force push, local Git or merge
to main was used. See M06-public-event-rates.md for concurrency and scope.

## Actual compiler evidence and next check

Target run 36264721932 / job 108467092139 for exact source c87c70d7 failed.
Its actual compiler artifact 10913791465 was downloaded through the GitHub
plugin and read. The ONLY source diagnostic is line 275: Set.mem_setOf_eq is
deprecated; use Set.mem_ofPred_eq. No dependent-motive or event mismatch remains
in that log. The warning-as-error gate was not changed or suppressed. The
current follow-up uses the compiler-requested name. The downstream example
and lint/axiom step were not reached, so this is not compilation acceptance.

Read the follow-up exact-SHA target jobs and actual logs next. Then inspect
normal/slow lint, transitive axioms, all-ReBeL and full CI without excluding
modules or weakening any gate. All of those new-source results are PENDING.
Original target list (107), global discovery (251), auditors, pins and workflows
are unchanged. M06-public-event-rates-validation.md records failure details,
archive provenance, local test results and the resume procedure.

## Current implemented slice

Three theorems bound actual conditioned-query native tails and unconditional
joint event-and-bad-native-gap probabilities; the public specialization also
covers impossible observations without constructing a posterior. Conditional
rates retain the ACTUAL event-mass denominator and positive threshold.
A genuine full-AOH budget-1/8 solver consumer has public-and-error-at-least-1/4
probability at most 1/2. Sharp diagonal controls reject dropping the event mass.
All older positive, hidden-selection, correlated-query and impossible-event
Lean controls are retained. The inherited public-posterior theorem is repaired
without changing its statement, supported-observation witness or joint law.

The four new Python tests cover 15,360 exact rational law/event/loss/threshold
cases, correlated posterior tags under a nonconstant stochastic kernel, rare
public events down to mass 1/1000003, and impossible-event boundaries. These
loss tables are not asserted to be CFR-generated native gaps.
Local full Python discovery passed 101 tests on the prepared follow-up source;
log SHA256 f2cb850cdf1b517e650c8a870d134c30b0c97a6a86b6ae648aec6a6b5c306130.
Exact c87c70d7 separately passed all 97 existing Python tests and both structural
checkers (3,054 items). No local Lean or PowerShell execution is claimed.
Python and structural checks do not establish Lean correctness or M06 completion.

## Earlier evidence is not current-source validation

The last historically validated conditioned-query source is
`6d111a4aa3060be10fa7e655d0dbfde13660cc7c`: target 36210326495 (107 modules,
1,669 axiom-audited declarations), ReBeL 36210326388 (251 modules, 4,848
declarations, 92 Python tests), full CI 36210326436, inventory 36210326380.
See M06-conditioned-query-repair.md. Subsequent public-posterior failures are
preserved in M06-public-posterior-repair.md and the new validation record.

## Remaining semantic boundary

Execution opponents are arbitrary fixed legal policies, never functions of a
private seed. The native gap still uses the SAME computed average comparison
opponent and ORIGINAL compatible full joint type kernels. Public-posterior
history equality neither makes tags independent nor transfers the value gap
to new posterior kernels/opponents. An unconditional JOINT public-and-bad-gap
rate is not a conditional guarantee after a rare public observation.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Independent carried-PBS re-solving identification, quantitative support/first-
exit rates, changing-opponent/PBS native and late rates, recursive re-solving
safety and CarriedResolveStepBounds remain. No event-mass floor, seed disclosure,
discarded finite-T residual or learner-convergence premise is introduced.
M07 is not started. From M07 onward use one integration branch per milestone;
temporary branches are justified by substantial experiments or parallel work,
not merely a new chat. Preserve and integrate exact-SHA accepted checkpoints.
