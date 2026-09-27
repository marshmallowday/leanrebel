# ReBeL status — recursive training proof-style repair pending Actions; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927 from re-read HEAD
7711b65f98851187eef0e05c66b5ba569e03ccf0. Main is
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. GitHub plugin access was
reconfirmed as marshmallowday/admin. Chat baseline:
9457c198126f3c8b7cb1045bbed2e0053788636f.

The retained-root batch and repair loop are accepted at 107bbaa.
CI 36351689781, checks 36351689813, targeted 36351689718 and inventory
36351689774 all succeeded on that SHA. Complete decoded logs contain 2059
targeted and 5200 global unique transitive axiom records, only the three
permitted axioms, all 122/264 module lint passes, full build/architecture/
rational runtime and 181 Python tests. The target manifest has 160 entries.
See M06-root-memory-107bbaa-accepted.md. This success does not verify new source.

The 7711b65 batch failed all three compiler jobs on the same proof-style
diagnostic at PBSRecursiveValueTarget.lean:108: letI was used in a proposition.
The local proof instance is repaired to let _ without changing statements,
premises, definitions, workflows or audit rules. PBSComposedValueTarget compiled.
Static architecture, rational runtime and 185 Python tests succeeded, but the
downstream example and complete lint/axiom audit remain unverified. See
M06-recursive-target-7711b65-failure.md for full job/artifact evidence.
The repaired source requires new exact-SHA Actions.

The pending batch integrates root targets with the actual composed oracle and
arbitrary-depth recursive solver. It preserves the same recursive child,
noisy learner trace, finite round count, joint PBS and original-game full
continuation. pbsRecursiveTrainingOutput returns both the existing average
policy and an information-state target vector, with separate policy and
numerical-mean guarantees. Empty schedules and zero-width cuts are explicit.
Three Lean integration modules and four Fraction tests are registered together.
See M06-recursive-target-batch.md. Expected validation is now 163 build targets,
125 targeted/267 global audit modules and 185 Python tests. Existing coverage
is retained; workflows and audit criteria are unchanged. No local Lean or
Python execution is claimed.

Unchanged 107bbaa source supports P-CFRD-TARGET via the append-only
coverage-updates/M06-root-target.json and M06-root-target-accepted.md.
SEARCH-FRONTIER/P-SEARCH-SETUP/P-SEARCH-LEAF remain accepted via their prior
journal. The historical coverage.json is still blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. All pinned proof sources are unchanged.

P-CFRD-AVERAGE, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The fixed-trace average-policy convergence clause is not accepted merely from
vector arithmetic or a finite-budget result. Remaining work also includes
small signed loss bounds for actual fresh recursive re-solving and complete
application of model-posterior comparisons in that analysis.

The target comparator is the mean of same-round original continuations.
It is not a final iterate, independently mixed joint policy, or asserted Nash
value vector. Absent labels use a total fallback and are not observed samples.
The stored model law is not equated to an unknown opponent's factual law.
Nash precision does not imply close policies or kernels. Printed R5 and
corrected/restricted statements remain separate; finite-T and child tolerance
are retained, and no network convergence is assumed.

Use only the main agent. Combine related implementations and fixes in large
dependency-ordered batches. Confirm separate workflows on each new SHA, then
schedule this chat once about 50 minutes after the branch update in Asia/Tokyo.
If still running, schedule another one-shot check about 10 minutes later.
Do not stop workflows or poll continuously.
