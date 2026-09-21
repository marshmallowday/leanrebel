# M06 independent sampling validation restart

The validation work started from c60f3b20d333557adb39509399b92029e64f005e
on rebel/m06-information-sampling-20260921. Changes were saved on
rebel/m06-sampling-validation-20260921 without local Git or force updates.
Main remains outside this integration.

The independent-sampling implementation and controls were checkpointed in
05d9ca6e and 047f5ee0, with documentation and proof repairs in f7f325f3,
52572a50 and 77cc57d3. The 52572a50 sampling build and normal module linters
passed. Its full ReBeL static audit rejected two uses of the change tactic;
77cc57d3 expresses the same proof with explicit profile equalities instead.

## Corrected diagnostic provenance

The initial restart note incorrectly attributed the inherited validation
failure to unused arguments. Fresh run 35569311710/job 106237384642, source
cbd937ac5a5c3af913081ca99befe9ad0b94426e, proved the actual issue was docBlame
on four named local instances. Those documentation omissions are repaired.
No type-class hypothesis, linter or allowed-axiom list was removed.

## Preserving the independently advanced supported-root branch

While preparing the evidence checkpoint, the existing branch
rebel/m06-sampling-checkpoint-20260921 was found at
28f789980d055943cffc171a3be2559744d2e3e4. It contains supported-root sampling
source 72a837daf5f5e295b38e3da67765b3f7f4278425, derived from the same c60f3b20
base. The merge retains all of that branch's proofs, controls, registrations,
and documentation, plus the independent-sampling additions. Its native
recurrence implementation split and the documented local instances coexist.
The extra supported-control instance also receives its missing docstring.

This integration is a compiler candidate until its own exact-source checks
complete. Neither parent's evidence is silently reused as validation of the
merged tree. All content-hashed M06 parent obligations remain pending.
