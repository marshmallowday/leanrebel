# M06 scalar stability continuation — 2026-09-25

## Exact starting point

This work starts from documentation checkpoint
`2e1de273b9164743decdd8a283b3249f34bf5600`, preserving the validated source
`4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5` and all predecessor evidence.
Work branch: `rebel/m06-scalar-stability-20260925`.
Main and predecessor refs are not moved.

The predecessor independent ReBeL run `36103763078`, diagnostics job
`107971751432`, was read through the GitHub plugin in this continuation.
It completed SUCCESS at `2026-09-25T07:18:47Z`, for exactly the source above.
The all-ReBeL compiler/lint/transitive-axiom step, rational solver,
ledger/adversarial checks, and tracked-file cleanliness steps all passed.
This resolves the pending independent CI recorded in STATUS.md. It does not
validate any new candidate or complete M06.

## Scope and next steps

Review the prior uncommitted scalar-value stability candidate against the
exact repository source. The intended slice compares two approximate Nash
solver outputs on the SAME joint PBS using cross-profile deviation bounds.
Keep scalar expected-value stability distinct from conditional value vectors,
outcome-law closeness, and small directed coupling cost. Preserve the explicit
counterexample to inferring a small directed cost from equal expected values.

Compile the focused Lean slice through the pinned repository CI, repair actual
diagnostics without weakening statements or gates, and inspect lint and the
transitive axiom output. Commit implementation and diagnostic checkpoints using
the GitHub plugin. Retain all existing targets, audits, dependency pins and
adversarial controls. Update STATUS and scoped coverage with exact evidence.

## Acceptance boundary

No new theorem is accepted by this documentation commit. Prior uncommitted
candidates are unverified until the compiler and semantic review succeed.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training conditional rates, later carried-PBS re-solving,
first-exit rates and CarriedResolveStepBounds remain separate obligations.
All repository access and Git operations use the GitHub plugin; downloaded
artifacts may be inspected offline without local Git operations.
