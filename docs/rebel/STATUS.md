# ReBeL status — M06 native-gap repair; M05 accepted

## Resume from the repaired native conditional-gap branch

Work branch: `rebel/m06-native-gap-repair-20260925`.
Initial source: `0bfa5ce2d1b67f5d14790e82e75e3db986b21fbd`, retained on
`rebel/m06-native-conditional-gap-20260925`.
Read `M06-native-gap-repair.md`, `M06-native-conditional-gap.md` and the
native coverage JSON. Re-read the actual branch head and its own Actions.
The repairs change proof bodies only. M06 is NOT complete; main is unchanged.

The initial targeted run `36128708985` / job `108050731655` compiled the
new general native-gap proof, then failed two simplifications in the negative
control. The existing pure-probability formula now closes those scalar goals.
The initial ReBeL run `36128708957` / job `108050823347` failed the static
architecture gate because one new `change` tactic entered the Analysis layer.
It is replaced by a named definition rewrite, with no change to the frozen
transport budget or audit script. These are observed failures of 0bfa5ce2,
not compile outcomes for the new repair. See the repair note for artifact
hashes and source provenance.

## Mathematical scope retained

The actual information-set CFR sampler preserves conditional payoff at each
supported root type against arbitrary FIXED opponents. Sampling retains the
same private uniform native index throughout continuation. The root-prefix
argument supplies the supported conditional-kernel identity.

Against the computed AVERAGE opponents, every native own-iterate has a
nonnegative Eq. (1) best-response gap. Thus the mean absolute native gap equals
the average policy's gap. Actual CFR supplies the finite-T bound. Own-law means
need no positive type-mass floor. Changed query laws retain exact density/cap
premises. The actual budgeted solve gives the prescribed positive mean bound.

The live HiddenTypes T=2 identity and budget-1/8 example use the real sampler.
The canonical exact-Nash opponent-sampling control has centered mean zero
and mean absolute drift 1/2. It forbids dropping the fixed-opponent condition
or commuting absolute value with expectation by signed cancellation alone.
It is not claimed to be solver-generated iterates.

## Validation obligations

The repaired source still needs its own compiler, configured lint and
transitive axiom results. New modules are in the umbrella and M06 targets,
and the unchanged global ReBeL auditor discovers them. The inherited
100-module exact-leaf audit is unchanged and does not itself certify these
two modules. No linter, test, target, dependency or axiom allowance is weakened.

Parent proof `5cf1369cf1e886650a90a4e027347dacf589d50b` now has successful
full CI `36125907627` / job `108041951383`. Its targeted run `36125907562`
passed with 100 linted modules and 1595 audited declarations. Its independent
ReBeL run `36125907531` / job `108041928085` remained in progress at the latest
inspection. Preserve M06-query-gap-validation.md and JSON; parent evidence
is never substituted for exact-source validation of the additions.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The native mean rate here is against fixed computed average opponents at one
fixed canonical slice. Independent changing-opponent/changing-PBS native or
late rates, actual carried support/first-exit and query-density control,
independent recursive re-solving safety and CarriedResolveStepBounds remain.
Keep private seed/history laws, zero-mass completions and actual/model belief
distinctions. Preserve the printed/corrected Theorem 3 statements, including
the nonzero finite-T residual when oracle error vanishes.

Main was last re-read at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
No learner-convergence premise substitutes for independent test-time safety.
