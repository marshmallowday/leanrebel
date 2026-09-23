# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-carried-iterations-20260923`.
This source extends the confirmed checkpoint
1a6bab28e1c04fa11ea692321ce32f3e312f576e with full-state disintegration and
arbitrary-future sampling-error transport. Check its own targeted CI and full
gates. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.

## Confirmed earlier slice in this branch

1a6bab28e1c04fa11ea692321ce32f3e312f576e passed M06 targeted run35833737612 /
job107092156662, including all 64 named supplemental lint/axiom modules.
Artifact10739080371 has GitHub-reported digest
8f07521eef5cb49549b972eb1fd83a08ae4ac6b1d6501cbd271852b903879b19.
Do not redo its compiled native sampler, event bound or twelve controls.
The current full-state extension requires its own exact-source acceptance.

## Native carried-PBS implementation

PBSCarriedSampling consumes the incoming joint model belief as a new root game,
draws an ACTUAL information-set CFR iterate, and retains its private profile
paired with the posterior propagated through that same iterate. It installs
into the existing finite runner. Missing beliefs retain the previous profile;
stopped stages make no solver query.

The one-step history comparison charges 2 * payoffBound * actualProbability(E),
where E means live, model belief exists, actual history outside model support.
The new history-first disintegration retains the NATIVE conditional joint law
of selected profiles and their model beliefs, so it proves the same estimate
after any identical future finite kernel reading the complete private state.
The comparison is analysis-only, not an alternative public strategy and not a
posterior-equality assumption. The exceptional mass is NOT proved to vanish.

M06-carried-iterations.md records declarations, fourteen theorem controls,
source mapping and the boundary. All three new modules remain in the analytic
root, target list and full supplemental auditor. No source row is promoted.

## Failed checkpoints, preserved for diagnosis

64bc087f / target35831741238 / job107085699414: two unused simp arguments in
PBSCarriedSampling. Repaired in71dc6950, which compiled both core modules.
71dc6950 / target35833033295 / job107089843494: two example elaboration errors.
Repaired by proof-local classical and explicit state unfolding in1a6bab28.
No theorem statements, model definitions, dependencies or audit gates weakened.

## Fully checked predecessor

b17501a84ec76c6cd996864144f4a616ac251a00 remains on the preserved
rebel/m06-recursive-envelope-20260923. Full CI35829793150/job107079581547 and
ReBeL35829793185/job107079633154 succeeded. The previous fresh-child evidence
at dd669071 is preserved in M06-fresh-envelope-validation.md.

## Remaining original obligations

Connect the genuine carried-PBS recursive execution to the parent value oracle
and derive source-dependent model-value drift and exceptional-mass estimates.
The native child here uses full-root CFR, not yet a recursively depth-limited
child oracle. The disintegrated comparator keeps the actual native conditional
private law; it is NOT recursion with independent averaged-PBS resets.
CarriedResolveStepBounds is not a discharged safety theorem. Preserve finite
outer T, nonzero numerical and child errors and the printed/corrected Theorem3
separation. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. No full M06, unrestricted Theorem3 or numeric-refinement claim.
