# M06 public-posterior compiler and architecture repair

Work branch: `rebel/m06-conditioned-query-20260925`. M06 remains incomplete.
The repair history below preserves the exact source diagnostics; none of these
failed jobs is treated as a completed compiler/lint/axiom gate.

## Current definition-unfolding repair

Parent: `0a5c886a2810b152893771582e46205a4c460780`.
Its target run 36262359018 / job 108460478671 compiled FinDistSelection.lean,
including both new projection/conditioning proofs. It then failed only at
PBSConditionedNativeGap.lean line 270: the simplifier left the named public
event folded on one side of the dependent conditioning equality. The actual
projected law and the expected law differed there only by the event definition.
No change to the theorem statement or possible-observation witness is needed.

The current repair rewrites the history marginal in the derived equality,
explicitly unfolds pbsInformationCFRPublicEvent and PublicBelief.condition, and
uses the resulting equality directly. The hidden-event control uses one
explicit singleton-membership simplification, avoiding a trailing proof step
after a rewrite that may itself close a singleton goal.

Actual target artifact: 10912787834.
ZIP SHA256: 27bce5822bd32e5d9b05e4955a2cfb1ae1373143d4dc21ab3565c6e7921f0fd2.
Log SHA256: 9f58c18f19ae698d737c8ece81ba28bb558d043ae85b440ea9c1e5b22432dc73.
The log identifies Lean 4.33.1 and exact parent source SHA. The downstream
example module and the complete targeted lint/axiom audit were not reached.

The parent all-ReBeL run 36262359068 / job 108460478888 passed the ACTUAL
unchanged source-width and Phase 2 architecture checks, dependency closure,
ledger/inventory/adversarial fixtures and rational Lean solver validation.
Its global compiler/lint/axiom step was still running when checked.
Parent source-inventory run 36262359116 / job 108460479118 succeeded.

Current prepared source bytes agree with plugin-created blobs:
- FinDistSelection: 97ddb4e2458d44f34be85c0f39b74f55bd148654 (unchanged).
- PBSConditionedNativeGap: e0dc8650922f92e0ca357755e39c2a287cbce834.
- Examples.PBSConditionedNativeGap: d268c31e0d4f5a7b2d7bc0a70b701f693bc6bdca.
New-source compilation, normal/slow lint, transitive axioms and all CI remain
PENDING this definition-repair push. No gate or dependency pin is modified.

## Earlier membership and architecture repair

First source: `3affbb7a48646ebaf9427463568e9aadbe51c7e6`.
Target run 36261898971 / job 108459202177 failed in FinDistSelection.lean:
three new equality-transport terms did not elaborate through set preimages or
under inferred indicator predicates (original lines 32, 52 and 60).
Actual targeted artifact: 10912462226.
ZIP SHA256: 64fe16bcbc6a028799564413faca2a179e6402bdbd19512c130de6048a0a440e.
Log SHA256: 8718adc1fad492fca01250405160f898e621d30db460020a05e657b8c47f929e.
All-ReBeL 36261898993 / 108459368799 failed the unchanged Phase 2 source
transport gate: Analysis=2 instead of 0, Math=4 instead of 1. The actual job
log was read through the plugin. Source inventory 36261899030 succeeded.

Repair `0a5c886a2810b152893771582e46205a4c460780` replaced those terms with
typed membership subgoals and ordinary equality rewriting, including the
example's hidden-selection control. The output-marginal proof was normalized
with explicit bind congruence and pure-map evaluation. No statement, event,
witness requirement, bound, example or original source obligation changed.

All 97 Python tests passed again with warnings treated as errors. Log SHA256:
d91286f315ee1417b76c6512bf435c9d63eb3e2e547c757dc8d94537331ce767.
An offline source scan restored Math=1 and Analysis=0; this was subsequently
confirmed by the actual unchanged parent CI architecture gate, as recorded
above. There is no local Lean or PowerShell execution claim.

## Semantic boundary

Read M06-public-posterior.md for the exact scope and candidate coverage.
Selected fixed-profile public HISTORY posterior equality is not fresh
independently re-solved carried-PBS safety. In particular, the actual execution
opponents in this theorem need not be the opponents used by a stored model
update in resolvedNextState; these posteriors must not be identified silently.
The native error remains at original type kernels against the SAME computed
average comparison opponent. No original coverage row is promoted.
