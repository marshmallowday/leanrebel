# M06 opponent/model transport: compiler and architecture repair

Branch: `rebel/m06-conditioned-query-20260925`. M06 remains incomplete.

## Original compilation failure

First source: `15b2f75176acd4068590b13fa2582d2e0f63b5e3`.
Target run 36270184129 / job 108482530932 FAILED compilation. Its actual
artifact 10915426722 was downloaded through the GitHub plugin and read.
ZIP SHA256: 323e26bd35393ffd59ee4d078cc3d1c6c0ca0f7ed22baa4f3c6b4fefbab2d500.
Log SHA256: 9add2720046dc0dcf02106b80a268467ffb5bca33c08548c3e9de03a80671b02.
The embedded source SHA and pinned Lean 4.33.1 match the intended source.

The new FinDistKernelVariation module compiled, including all five kernel and
lost-support proofs. The analytic module had two unsolved goals (and resulting
unused-simp-argument errors): simplification did not expose the partially
applied zero-step kernels, and simplification left the optional-conditioning
branch undecided at the named model law.

First-source ReBeL run 36270184087 / job 108482676277 passed the actual width,
static architecture, ledger/adversarial fixtures and Lean rational-runtime
steps; global validation was still running when inspected. This is not claimed
as a successful global gate.

## First repair and unchanged architecture gate

Repair `af26c3a74e8c840d4709d28883de2e385829cddc` explicitly exposed the two
expected types before applying bind-pure and dif_pos. Its ReBeL run
36270651313 / job 108483926699 FAILED the original Phase 2 source-transport
gate: TRANSPORT_ANALYSIS_SOURCE was 2 rather than the required 0. The complete
actual job log was read through the GitHub plugin. Its source-width check
passed; compiler/lint/axiom stages in this ReBeL job were skipped.
The diagnostic artifact is 10915791285 (architecture log), ZIP SHA256
bfd982be6061199cea5069fca4f90f085c94f1fa3df82cc42b56bee7018ccdaa.
Its separate targeted compiler run 36270651340 was not yet complete when this
architecture repair was prepared; no success is inferred from it.

The current repair supplies a named zero-step kernel equality by reflexivity
and uses it in ordinary simplification. The supported Option-valued update is
proved directly by dif_pos using its constructed support witness; no explicit
type-adjustment tactic is needed. No audit code or expected count is changed.
The source scan of all new modules contains no transport tokens; the real
unchanged Phase 2 gate must confirm the total on the new source.

Only the two proof bodies differ from the first source. No statement, constant,
event, initial law mismatch, example, validation gate or dependency pin is
weakened or removed. The example module, normal/slow lint and transitive-axiom
checks must be inspected on the latest repair SHA.

## Independent finite diagnostics and remaining boundary

Offline 103 Python tests passed again on the exact first-source snapshot,
including 16,384 exact rational kernel/horizon comparisons, with warnings as
errors. Log SHA256: 597268a5d2b74cf34306eb6647ed8a6972c13a16824eef63cf2e3510a6563baa.
Coverage/inventory still have 3,054 original items and unchanged statuses.
No local Lean or PowerShell execution is claimed.

The repair source and subsequent validation remain pending until the new
GitHub Actions logs are inspected. See STATUS and the source candidate manifest.
This compiler repair does not prove source-charge smallness, changed-PBS native
value stability, recursive test-time safety or CarriedResolveStepBounds.
