# M06 opponent/model transport: compiler repair

First source: `15b2f75176acd4068590b13fa2582d2e0f63b5e3`.
Branch: `rebel/m06-conditioned-query-20260925`. M06 remains incomplete.

Target run 36270184129 / job 108482530932 FAILED compilation. Its actual
artifact 10915426722 was downloaded through the GitHub plugin and read.
ZIP SHA256: 323e26bd35393ffd59ee4d078cc3d1c6c0ca0f7ed22baa4f3c6b4fefbab2d500.
Log SHA256: 9add2720046dc0dcf02106b80a268467ffb5bca33c08548c3e9de03a80671b02.
The embedded source SHA and pinned Lean 4.33.1 match the intended source.

The new FinDistKernelVariation module compiled, including all five kernel and
lost-support proofs. The analytic module had two unsolved goals (and resulting
unused-simp-argument errors):

1. In the zero-fuel execution proof, simplification did not expose the partially
   applied zero-step kernels. The repair explicitly changes to the definitionally
   equal pure kernels, then uses the existing bind-pure identities.
2. In the supported carried-update proof, simplification left the dependent
   optional-conditioning branch undecided. The repair explicitly identifies
   the Option-valued condition at the named model law and uses dif_pos with
   the actual positive-support witness.

Only these two proof bodies are changed. No statement, constant, event, initial
law mismatch, example, validation gate or dependency pin is weakened or removed.
The new example module, normal/slow lint and transitive-axiom checks were NOT
validated by this failed target; they must be inspected on the repair SHA.

First-source ReBeL run 36270184087 / job 108482676277 passed the actual width,
static architecture, ledger/adversarial fixtures and Lean rational-runtime
steps; its global validation was still running when inspected. This is not
claimed as a successful new-source global gate.

Offline 103 Python tests passed again on the exact first-source snapshot,
including 16,384 exact rational kernel/horizon comparisons, with warnings as
errors. Log SHA256: 597268a5d2b74cf34306eb6647ed8a6972c13a16824eef63cf2e3510a6563baa.
Coverage/inventory still have 3,054 original items and unchanged statuses.
No local Lean or PowerShell execution is claimed.

The repair source and subsequent validation remain pending until the new
GitHub Actions logs are inspected. See STATUS and the source candidate manifest.
This compiler repair does not prove source-charge smallness, changed-PBS native
value stability, recursive test-time safety or CarriedResolveStepBounds.
