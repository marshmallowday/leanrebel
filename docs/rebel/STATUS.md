# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-carried-iterations-20260923`.
This checkpoint repairs the two example elaboration errors on source
71dc6950ee683eea4361189cccbba30367436d52 without changing the sampler or bound.
Check this exact HEAD's targeted CI and full gates before integration.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.

## Current native carried-PBS slice

PBSCarriedSampling consumes the incoming joint model belief as a new root game,
draws an actual information-set CFR iterate, and retains its private profile
paired with the posterior propagated through that same iterate. It installs
into the existing CarriedResolveStage/executeCarriedResolves finite runner.
Missing beliefs retain the previous profile; stopped stages make no query.

FinDistEventError and pbsCarriedCFRResolver_actual_error derive a single-step
comparison to the same child's own-reach average, charging
2 * payoffBound * actualProbability(live state with unsupported actual root).
No support domination or posterior equality is assumed. No claim is made that
this mass vanishes, or that equal history marginals permit substituting the
complete private-profile/posterior state in later recursive stages.

Exact declaration scope, source mapping and controls: M06-carried-iterations.md.
All three new modules are in the analytic root, M06 targets and all-declaration
normal/slow-lint axiom auditor. Original source coverage rows remain pending.

## Feedback to preserve

64bc087f target 35831741238/job107085699414 compiled the finite-law error module
and inherited targets; PBSCarriedSampling failed only on two unused simp
arguments at lines138 and145. They were removed without disabling lint in
71dc6950. Source inventory35831741268 succeeded on64bc087f.

71dc6950 target35833033295/job107089843494 compiled BOTH FinDistEventError and
PBSCarriedSampling. Its new examples failed at line34 on a local Decidable
instance and line103 on the unexpanded state-history field. The current patch
adds proof-local classical and unfolds the named example state in the stopping
proof. It changes no theorem statement, linter, model definition or dependency.
Source inventory35833033335/job107089843259 succeeded on71dc6950.
ReBeL35833033360/job107090241715 passed static architecture and runtime controls;
its later compiler/audit step was not complete at recording.

## Fully checked predecessor

b17501a84ec76c6cd996864144f4a616ac251a00 on the preserved
rebel/m06-recursive-envelope-20260923 passed full CI35829793150/job107079581547
and ReBeL35829793185/job107079633154. Its fresh-child source slice dd669071
passed target35828662651/job107075968088. Do not redo those completed repairs.
See M06-fresh-envelope-validation.md for the previous exact-source evidence.

## Remaining original source obligations

Connect genuine carried-PBS recursive execution to the parent value oracle,
and derive source-dependent value-drift and exceptional-mass bounds. The
current native child uses full-root CFR at its prescribed finite horizon,
not yet a recursively depth-limited child oracle. CarriedResolveStepBounds is
not a discharged safety result. Preserve finite outer T and nonzero numerical
and child errors. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3
remain pending. No full M06, unrestricted Theorem3 or numeric-refinement claim.
