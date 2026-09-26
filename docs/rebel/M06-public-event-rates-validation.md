# M06 event-tail source validation

## Actual inherited compiler diagnostics

The work branch is `rebel/m06-public-event-rates-20260927`, descended from
`a76f1f32403f3cc1834d8f39d11b9802626ee592` through planning commit
`65a1612311836767d6a27c1ce47de82e1611cd46`. See the scope document for the
concurrent ref advance and the deliberately unused stale repair commit.

Base target run 36264124596 / job 108465401160 completed with FAILURE.
The actual decoded job log was read through the GitHub plugin. It records
exact source a76f1f3, Lean 4.33.1 and pinned mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
FinDistSelection and the prerequisites compile. The only target source error
is PBSConditionedNativeGap.lean:273: dependent simplification leaves the
preimage of a set-builder on one side and the explicit event set-builder on
the other. The projected conditional support proof and history-law transport
are retained. The downstream example and target lint/axiom step were not reached.
Artifact ID 10913219197; reported ZIP SHA256
f98ab92e6cd69156521b08c9072ff9ce17acf9f83103c0c221f70784183672b0.
This artifact digest is from the actual job log, not a local artifact download.

The initial proof-only repair added Set.preimage and Set.mem_setOf_eq to the
restricted dependent simplification. It did not change the public event,
theorem statement, positive-support witness or canonical joint history law.
The base's explanatory proof comments are preserved.

## New tail statements and controls

The conditioned-tail theorem composes the existing finite-T mean theorem with
FinDist.markov_inequality, keeping B_T / (actual event mass * threshold).
The unconditional event-tail theorem applies probOf_le_expect_div directly to
the actual tagged execution. Its observable is the original native gap at the
retained tag; the tag marginal theorem reduces its mean to the established
native CFR mean bound. Restricting to an event only restricts the bad set; no
possible-event certificate is required. The public theorem is this statement
at the canonical public-trace event, not a new posterior-kernel value estimate.

A live full-AOH budget-1/8 solver has public-and-error-at-least-1/4 probability
at most 1/2. The diagonal finite-law diagnostic has conditional threshold-one
tail one, weighted tail one half, and contradicts a conditional coefficient
with the actual event mass omitted. The diagnostic is not a claimed CFR gap
table. All earlier controls remain unchanged.

Initial source blobs prepared through the plugin:
- Main: fc18d3354976dce4c1d70bcff285689419de2c9d.
- Examples: 5d3d3572bc110241c7dfc1513e5fbbb85d99c663.

## Source checkpoint c87c70d7: observed failure, not acceptance

Source commit: `c87c70d7b1c6dce3d3699d2908eea72811d8e713`.
Target run 36264721932 / job 108467092139 failed compilation. The actual
m06-targeted.log from artifact 10913791465 was downloaded through the GitHub
plugin, its archive hash verified locally, and its contents read. It identifies
source c87c70d7 and Lean 4.33.1. The ONLY source diagnostic is:

`PBSConditionedNativeGap.lean:275:28: Set.mem_setOf_eq has been deprecated:
Use Set.mem_ofPred_eq instead`.

Thus the preimage normalization removed the prior type mismatch, but the
warning-as-error gate correctly rejected a deprecated declaration. The build
must still be rerun: the downstream example and target audit were not reached.
The follow-up replaces that single simp name; it does not suppress warnings,
remove assertions, modify theorem statements, or change any validation gate.
Follow-up main blob: `c97f2c1ebe3fe079a3603d1d01d5ef864fa31cd5`.

Compiler-artifact ZIP SHA256:
435504e10073566bb14b6811a86c3f10a82cc6f635f47f6104bead3ed9498eef.
Extracted compiler-log SHA256:
bf3591b64cce5152fbe123206b0f8204bf9dd56c9a6d82e7b5a79e3e1eed52e7.

Associated c87c70d7 runs are ReBeL 36264721941 (diagnostics job 108467164912),
full CI 36264721795, and source inventory 36264721966. The inventory job
108467091975 reported success; this badge is not Lean evidence. When read,
the ReBeL step metadata showed successful line-width, architecture, structural,
Python and rational runtime steps, with compilation/auditing still running.
These step summaries are not substituted for the final full actual logs.

## Reproducible local diagnostic tests, through plugin-sourced bytes

ReBeL source artifact 10913244354 contains the exact c87c70d7 tracked tree,
source-commit.txt and source-sha256.txt. It was downloaded with the GitHub
plugin and extracted without a .git directory or any local Git operation.
ZIP SHA256: 5ae36102f9c8c5b2e3dfc0ad99ff38268a4feaab3afdb45e1d839fb5b67a2f2a.
Tracked-source TAR SHA256:
dc50270ed49e5279301f68f988a7c27fc69eb194a1eff2a557737084acb9ff15.
Both digests were verified. Exact-source full Python discovery passed 97 tests:
`python -W error -m unittest discover -s scripts/rebel/tests -v`.
Log SHA256: bb384907c543b8902b775ca42cdd8c15f7f2c4948fc9320210ed0825770849dc.
Both check_coverage.py and check_inventory.py passed with 3,054 structural items;
neither was invoked with a Lean option. The two changed Lean files had zero
UTF-16 line-width violations above 100.

The prepared follow-up adds test_public_native_tail.py and changes only the
one deprecated Lean name. Full Python discovery then passed 101 tests.
Log SHA256: f2cb850cdf1b517e650c8a870d134c30b0c97a6a86b6ae648aec6a6b5c306130.
The four additional tests exhaust 15,360 rational law/event/loss/threshold
combinations, check a stochastic tag-preserving execution with correlated
posterior tags, exhibit sharp rare PUBLIC event mass 1/1000003, and reject
posteriors for impossible events while preserving their zero joint rate.
The helper conditioning and pushforward functions are reused from the existing
public-posterior tests. No pre-existing tests or expected audit counts change.
No local Lean or PowerShell execution is claimed.

## Current acceptance boundary and resume action

Follow-up compiler, example, normal/slow lint, transitive-axiom, all-ReBeL and
full CI outcomes are PENDING its exact-source push. Existing auditors, 107
configured targets, 251 globally discovered modules, workflows, pins and source
paper obligations remain unchanged. Read exact-SHA jobs and actual logs before
promoting any candidate. Do not repeat the already documented static/unit
checks as a replacement for the missing Lean evidence.

Native gaps still retain original joint type kernels and the same computed
average comparison opponent. Fresh carried-PBS identification, changing-
opponent/PBS native and late rates, support/first-exit rates and recursive
CarriedResolveStepBounds remain open. M06 and Theorem 3 are incomplete.
