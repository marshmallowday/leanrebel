# M06: fresh carried-PBS solving and the missing-model branch

## Scope and checkpoint status

Supplemental project coverage for ROADMAP M06; not a replacement for the
hashed source inventory. Branch: `rebel/m06-carried-resolve-20260923`.
The first source checkpoint `eb59ccf754862f1e584deeee4eb3a44df39cce60`
reached the new module in run `35822279205`, job `107056486306`. Its one-step
proof failed on a missing direct import and an unreduced resolver match.
The successor retains all statements and adds whole-schedule theorems.
Compiler, lint and axiom acceptance must be recorded for the successor SHA.

## Implemented interfaces and proposed theorems

`CFRDInformationResolve` constructs a fresh uniform draw over the actual
information-set CFR iterations at the stored correlated joint PBS. Its count
is `pbsInformationConditionalRounds`, including the computed mass floor and
positive child tolerance. `some belief` invokes this new solve; `none` keeps
the newest complete policy in private memory, not the original parent policy.

`cfrDInformationResolveStages` trains each child for its full remaining
horizon while executing the current interval only. Existing
`carriedMemoryStep`, `carriedBeliefUpdate` and `executeCarriedResolves` retain
the selected draw and propagate the stored PBS. The unknown opponent is
never an input to the resolver. No independent history runner is introduced.

The core one-step missing-PBS identity is lifted by induction to
`cfrDInformationResolveStages_run_none`: every finite remaining schedule has
the same complete history law as the current incumbent. Therefore
`cfrDInformationResolveLoss_none` is exactly zero for every history observable.
`cfrDInformationResolveLoss_supported_part` isolates the remaining loss on
available-PBS states under an arbitrary actual state law, without assuming
that the actual and model laws agree or have the same support.

The local sampled-child deviation bound is derived from the actual child
recurrence in `cfrDInformationResolveDraw_gain_le`; the allowance remains the
model law's positive mass floor times the positive child tolerance. This is
an averaged model-PBS theorem, not an individual-iterate or arbitrary-root
optimality guarantee.

`cfrDInformationRecursivePlay` connects the actual noisy sampled-value parent
from the previous checkpoint to this fresh finite carried-solving schedule.
The empty-schedule theorem recovers the exact retained parent construction.

## Boundaries that remain open

The missing-PBS branch preserves the incumbent and adds zero replacement
loss. It does NOT show that a selected incumbent is individually safe, or
that newly solved supported branches preserve incumbent exploitation against
one weak fixed opponent. The latter inference has a preserved counterexample
in `Examples/CFRDEquilibriumReplacement`.

A populated stored PBS need not support every actual history under an unknown
opponent. The draw-law identity still uses its explicit model root law. A
derived counterfactual opponent-value envelope on the changed carried laws,
followed by the full supported-branch recursive safety bound, remains open.
The retained-parent finite-T/noise/positive-child-loss theorem must not be
presented as that full recursive result.

The `none` fallback is an explicitly chosen completion policy, not a proved
identity with every behavior of the paper or official numerical code.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
No source row, axiom allowlist, linter, test or dependency pin is weakened.
