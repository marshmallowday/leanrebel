# M06 retained-root batch: bc9b95b compiler feedback

Source bc9b95ba04dae6ed0c8580a72c8547b982a6eeed is NOT accepted.
Continue the same branch rebel/m06-kernel-value-repair-20260927 from this
re-read HEAD. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Account marshmallowday/admin was reconfirmed. This repair changes proof
elaboration only; definitions, theorem statements and validation rules remain.

## Complete job evidence

All run head_sha values match bc9b95ba04dae6ed0c8580a72c8547b982a6eeed.
- [CI 36345031434](https://github.com/marshmallowday/leanrebel/actions/runs/36345031434),
  job 108692377608: failure in full build.
- [ReBeL checks 36345031476](https://github.com/marshmallowday/leanrebel/actions/runs/36345031476),
  job 108692377471: failure in proof-module build;
  snapshot job 108692377700 succeeded.
- [M06 targeted 36345031460](https://github.com/marshmallowday/leanrebel/actions/runs/36345031460),
  job 108692377584: failure in declared-target build.
- [Inventory 36345031498](https://github.com/marshmallowday/leanrebel/actions/runs/36345031498),
  job 108692377543: success, 181 tests in 9.971s.

Complete decoded logs from all four validation jobs were obtained through the
GitHub plugin. The three compiler jobs report the same six errors below.
FinDistRetainedLabel compiled successfully. Checks passed static architecture
(LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0), 181 Python tests in
9.562s and RATIONAL_RUNTIME_PASS. Complete new-source normal/slow lint and
transitive-axiom records were not reached; the batch remains unaccepted.

Artifact metadata: targeted 10940545770,
sha256:87b5b54defbfe8e1f937c0f270a2bf0b282f3fb40a0a66469baa8668adeca7a6;
global diagnostics 10941160374,
sha256:c16c17792d1941109b88436f51e2448089b8f836d6c62d6a2f4470c30b31087e;
source snapshot 10940311778,
sha256:c0a82c1f410cabc801118d03fe74befa8a72270b640c77c93046c15c1e69fb77.
CI and inventory had no uploaded artifacts. Archives were not downloaded;
the complete decoded job logs supply compiler evidence.

## Six errors and combined repair

All locations are in CFRDValueTargetMemory.lean at the failed source.
1. Line 137: prefixAt_eq_of_length_le could not infer the snapshot AOH from
   a bare Nat.le_refl 1 proof. Pass the concrete rootedSnapshot explicitly.
2. Line 161: rewriting the prefix identity leaves reduction of the root
   signal and Option.map unresolved. Finish that observed goal with rfl.
3. Line 185: the readout theorem has Option.map, but the recoding expression
   used Option.bind with an optional label. Use the same nonoptional label
   and Option.map throughout, and simplify the mapped some constructor.
4. Line 223: reverse rewriting the conditional-map theorem left unresolved
   higher-order map/value arguments. Instantiate the law, typed state reader,
   label and value in a local equality before rewriting.
5. Line 318: the rooted payoff function and Option.elim callback did not
   unify through partial application. Prove their function equality by
   extensionality and cases on state, rewrite it, and supply the actual
   parent profile explicitly.
6. Line 377: the original-game identity did not rewrite the partially
   applied two-argument target trace under its mean. Prove equality of the
   complete trace functions with funext n tag before rewriting the bound.

All changes are grouped in one repair commit. No conclusion is weakened and
no new hypothesis is introduced. The existing test suite and workflows remain
unchanged. The preserved surface is 160 build targets, 122 targeted/264 global
audit modules and 181 Python tests. No local/plugin Lean or Python execution
is claimed. Earlier d2af110 success is not verification of this repaired source.

Root-target/source acceptance, useful small costs for the actual recursive
solver, full recursive posterior comparison and remaining SEARCH-CFRD,
SEARCH-ERROR/SAFE-THEOREM3 obligations remain pending.
