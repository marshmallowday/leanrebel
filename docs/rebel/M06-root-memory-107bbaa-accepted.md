# Retained-root value batch accepted at 107bbaa

Work branch: rebel/m06-kernel-value-repair-20260927.
Exact accepted SHA: 107bbaa5d7017e0dc92a85acfab73b90ac81618d.
Batch began at bc9b95ba04dae6ed0c8580a72c8547b982a6eeed and was repaired
through 0e71e36f7d5521b2875c21713ad7024602e6f6a3. The chat baseline is
9457c198126f3c8b7cb1045bbed2e0053788636f. Read-only plugin checks reconfirmed
marshmallowday/admin, this HEAD, and main
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 before new work.

## Exact-SHA Actions evidence

All four runs completed successfully and reported the accepted head_sha.

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36351689781](https://github.com/marshmallowday/leanrebel/actions/runs/36351689781) | 108711471388 |
| ReBeL checks | [36351689813](https://github.com/marshmallowday/leanrebel/actions/runs/36351689813) | 108711471281 |
| M06 targeted | [36351689718](https://github.com/marshmallowday/leanrebel/actions/runs/36351689718) | 108711470862 |
| Source inventory | [36351689774](https://github.com/marshmallowday/leanrebel/actions/runs/36351689774) | 108711471302 |

Complete decoded job logs were read via the GitHub plugin. The multiline
transitive records were parsed in full: 2059 unique targeted and 5200 unique
global declarations, with no axioms outside propext, Classical.choice and
Quot.sound. All 122 targeted and 264 global module lint passes were present;
normal and slow lint, umbrella/full build, architecture and rational runtime
passed. CI also reports the full-library LintAll pass and clean tracked tree.
The declared build manifest has 160 targets.

ReBeL checks: LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS, 181 Python tests in 9.368 seconds.
Inventory: 181 tests in 9.901 seconds. The math module's five declarations
are covered directly by targeted lint/axioms; global ReBeL dependencies also
retain transitive axiom checking. No local Lean or Python execution occurred.

Artifact metadata was inspected; binary archives were not downloaded:
CI 10942313050 (sha256:0920eedb8be160643adbec45b1560c23716f3b018c2393a8ab1896484baf0813);
global 10943311368 (sha256:2c3128825fef6feb1ecb46f61aef8a477c0bf172d3e1728cb04f3d242eea949c);
targeted 10943086240 (sha256:71185d6ed197acde9d86025e2a0b4220960a653f4236ebfb965a8cd7f5ce1677);
source snapshot 10942870387 (sha256:8371b9055acfa28ca6489fbf4c4320aa464df8fc4abea3de64f0ab2532016c07).
Snapshot job 108711471481 succeeded; inventory had no artifact.

## Source and meaning

- FinDistRetainedLabel.lean: a947b7b28210bf5018f33bdb3497365d835b519c.
- CFRDValueTargetMemory.lean: 04f9c66ca14a0c040f8a8a60edb35a574f238bc9.
- Examples/CFRDValueTarget.lean: 5896a36adc4e4245b55385bab8aa1abfbd3c3025.
- CFRDValueTarget.lean remains 1b1a4bdfc6f089364c8aa0b059bc96b5bb0eb86f.

Supported kernel transitions preserve the remembered root label. Conditioning
commutes through the canonical runner and its original-game decoder. The root
type law and support are exactly those of the correlated input joint PBS,
including rare types and early stopping. Numerical accuracy compares the
backed-up vector with the mean of actual same-round continuations.

Acceptance covers these dependency results, not convergence of target vectors
to Nash values, fixed-trace asymptotic convergence, network training, or small
loss from independent fresh re-solving. New recursive training-output source
requires its own exact-SHA Actions and semantic review. M06 remains incomplete.
