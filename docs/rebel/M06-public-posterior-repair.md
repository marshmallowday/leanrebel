# M06 public-posterior compiler and architecture repair

## Observed first-source results

First source: `3affbb7a48646ebaf9427463568e9aadbe51c7e6` on the existing
`rebel/m06-conditioned-query-20260925` branch. M06 remains incomplete.

Target run 36261898971 / job 108459202177 FAILED in FinDistSelection.lean:
three proof-side equality transports did not elaborate through set preimages
or under inferred indicator predicates (original lines 32, 52 and 60).
The actual targeted log was acquired through GitHub artifact 10912462226.
ZIP SHA256: 64fe16bcbc6a028799564413faca2a179e6402bdbd19512c130de6048a0a440e.
Log SHA256: 8718adc1fad492fca01250405160f898e621d30db460020a05e657b8c47f929e.
The log identifies Lean 4.33.1 and the exact source SHA. Downstream public
posterior declarations were not yet compiled; no lint/axiom success is inferred.

All-ReBeL run 36261898993 / job 108459368799 FAILED the unchanged Phase 2
source transport gate before Lean compilation. The actual plugin job log shows
TRANSPORT_ANALYSIS_SOURCE=2 instead of 0; TRANSPORT_MATH_SOURCE=4 instead of 1.
Source-inventory run 36261899030 / job 108459202310 succeeded.
Full-CI run 36261899009 / job 108459369769 was still running when checked.

## Focused repair

Replace exactly those new explicit transport terms with typed membership
subgoals and ordinary equality rewriting. The example's hidden-selection
control uses the same rewriting discipline. No theorem statement, event,
witness requirement, numerical bound, example, source obligation or validation
configuration is weakened. The existing output-marginal example proof is
normalized by explicit bind congruence and pure-map evaluation, avoiding an
unnecessarily broad simplifier list before its first successful compilation.

Prepared and plugin-created replacement blobs agree:
- FinDistSelection: 97ddb4e2458d44f34be85c0f39b74f55bd148654.
- Examples.PBSConditionedNativeGap: 71e1d443036e28879a49da11091c750aeb497e1f.
The main PBSConditionedNativeGap module remains 939f440368cec193413f9f80f0104b058fbe1e72.

All 97 Python tests passed again, warnings treated as errors. Log SHA256:
d91286f315ee1417b76c6512bf435c9d63eb3e2e547c757dc8d94537331ce767.
An offline source scan using the unchanged Phase 2 token pattern with comments
and strings removed now counts Math=1 and Analysis=0. The only Math token is
the inherited declaration in FinDist.lean. This offline check is NOT execution
of the PowerShell phase audit and is NOT Lean compilation. The actual unchanged
architecture gate, compiler, normal/slow lint and transitive-axiom checks must
run on the new repair source SHA. All are PENDING this repair push.

Read M06-public-posterior.md for the exact semantic scope. In particular,
selected history-law equality is not fresh independently re-solved carried-PBS
safety, and the native error still uses original type kernels and the fixed
computed average comparison opponent. No original coverage row is promoted.
