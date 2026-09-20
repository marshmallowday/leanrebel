# M06 finite-child integration: exact-source evidence and semantic review

This records a verified intermediate dependency slice, not M06 acceptance.
Proof source: f4671e429e7a221999e661f862e15f38d2ade700.
Proof branch: rebel/m06-finite-child-20260920.
Restart/evidence branch: rebel/m06-finite-child-checkpoint-20260920.
The evidence commit changes no Lean source, dependency, or verification gate.

## Saved stages and restart continuity

The actual remote at entry was 919213d60fbfc767b8f0f862e57503fffeb4c714 on
rebel/m06-finite-plan-rm-20260920, already beyond the old c16beb4d chat summary.
Its finite solver, mass-floor proofs and conditional budgets were retained.
All changes below are descendants. Main remained
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No force updates were used.

| Commit | Stage |
|---|---|
| 838123baca1e180db6c2a4a4fc8d2ca6f1d0f10a | Repair the Boolean finite-sum and proof-style example, preserving its statement. |
| cfd9a8f96463d5921b3e7ae7cd3ca1decf8083ef | Construct actual finite public children and full played/deviation laws. |
| 274db56cb56d8cfbd3a22827b30d2ccc5dabdc83 | Connect posterior-specific budgets and zero-own-reach completion. |
| d6db5e466ea4e069be4e02c7878f179b4c645f50 | Connect the finite children to the noisy actual outer recurrence and security; register all four modules and controls. |
| f4671e429e7a221999e661f862e15f38d2ade700 | State the posterior and numerical root budget explicitly in the child-Nash proof. |

M06-status-before-finite-child.md has the exact inherited STATUS bytes and blob
d88f3dc9fadad19f48c31f6d55c8b99a397011f9. Older source and evidence branches
are preserved, not rebased, deleted, or replayed as new work.

## Exact-source compiler, axiom and lint evidence

Toolchain: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Commands: lake build $(cat scripts/rebel/m06-targets.txt), followed by
python3 scripts/rebel/audit_exact_leaf.py. The global gates remain separate.

Target run 35517749018, job 106096437386: SUCCESS in every step.
All 61 declared targets built. First build: 3,316 Lake jobs; the supplemental
build reports 3,305 jobs. The supplemental audit inspected 243 complete
transitive declaration records in 23 modules, including private declarations.
All 23 normal/slow module lint passes and EXACT_LEAF_VALIDATION_PASS are present.
No error: or warning: record occurs. Every axiom set is a subset of
[propext, Classical.choice, Quot.sound]. The four new modules account for
33 of the compiler's records, including generated equations and local instances;
their source contains four definitions, 14 general theorems and seven controls.

Successful artifact: 10607222724, m06-targeted-f4671e429e7a221999e661f862e15f38d2ade700.
ZIP SHA256: 050765fc86b058675448347b0e7202c7434ec3e2bbdda199e44e231779f87c0a.
Raw complete log SHA256: 09f06129f72dd4fd54d1be45c2910741212e8289c146c0b14ad92b37dc4d57d4.
M06-finite-child-axioms.txt is a selected normalized excerpt of the 33 new-module
records, not a file claimed to have the complete raw-log hash.

| Same proof source f4671e42 | Run / job | Observed state at recording |
|---|---|---|
| Source inventory | 35517749009 / 106096437327 | Success |
| Full repository build/lint/architecture | 35517749006 / 106096472731 | In progress; not accepted as passed |
| Full ReBeL compiler/lint/transitive axioms | 35517749020 / 106096471791 | In progress; not accepted as passed |

Read final exact-source results before any milestone acceptance or integration.
A later documentation commit has separate runs and cannot relabel a source run.

## Failures, repairs and inherited evidence

919213d6 target run 35514530420/job 106088116753 built the finite solver but
rejected its Boolean example: the supplied finite instance did not reduce
through Fintype.sum_bool, the false equality needed explicit simplification,
and letI was disallowed by the proof-style linter. 838123ba enumerates the
actual finite carrier and uses let; no test statement or gate was weakened.

838123ba passed target 35516637178/job 106093582774: 3,312 Lake jobs, 210 complete
transitive axiom records, and 19 normal/slow module lints. Its artifact is
10607520127; ZIP SHA256 c703852a44db0f32dce4a0584f9ccb6629356db0e87da16f722960a1ef30fa88.
This independently inspected parent success is not reused as child validation.

The cfd9a8f9 target 35516904648/job 106094276315 was cancelled by a subsequent
branch update; no success is claimed for that run. d6db5e46 target
35517440285/job 106095646489 failed while inferring the omitted root-error
argument and posterior in cfrDFiniteChildProfile_isNash. The next commit
specifies both expressions; the final f4671e42 run validates the entire chain.
The earlier validation-budget run 35511013150/job 106078847374 was also reread
as successful, separately from these later finite-plan and child sources.

## Exact snapshot and offline checks

Snapshot artifact: 10607546267 from ReBeL run 35517749020.
Snapshot ZIP SHA256: 33ce4c3a4c0a7d5fe50d5dce76b485e65784041efaa1eecf7ae0e61826358077.
The snapshot's source-commit is the full f4671e42 SHA above. All four new files,
import root, target list and supplemental auditor were compared byte-for-byte.
Offline work used only plugin-downloaded content; no local git or direct
GitHub access was used. Original and final source archives were also compared.
No source file was removed; all original imports and targets are retained.
The supplemental auditor differs only by adding the four module names.

All 76 existing Python tests passed with warnings-as-errors on the exact final
snapshot. Coverage and inventory structural checks passed with all 3,054
original expanded rows retained: 64 verified, 41 qualified, five refuted,
406 context-indexed, one empirical, 2,537 pending. This is not a completion
percentage. These checks do not substitute for Lean proof or semantic review.
All 499 non-Experimental Lean files meet the unchanged 100-column limit.
lean-toolchain, lakefile.lean, lake-manifest.json and coverage.json are unchanged.

| New proof file | SHA256 |
|---|---|
| CFRDFiniteChild | 4ca2c70b50b1968cf98d0886cec603c71ed63d8469ef6b12617b8b59ccd57459 |
| CFRDFiniteContinuation | b4ad317dbc4c0e14a77a74772ad2aaec9d87b746090511dcef578f7a4fae766c |
| CFRDFiniteDriver | 4a2d2220395b55df45986d324cc18f18cf6391644076a0fb12579b5a3fea661d |
| Examples/CFRDFiniteChild | 342349e034e90d029d4d797d339587cd60f73db4ebede4537f70c1aa7856269e |

## Semantic review and variant boundary

Theorems use canonical full-AOH execution, finite histories/actions, legal
fallback policies, real bounded zero-sum utility, and all complete legal
behavioral deviations. The clock and recall come from the existing full-AOH
interface. Positive child tolerance is essential; zero-error finite solving
is not promised. Positive outer iteration count is required by averaging.

At a factual live PBS, its minimum positive history atom m is computed.
One common finite horizon meets root error epsilon=m*L for L>0. Each supported
type has probability p>=m, so the proved approximate-Nash bridge gives
conditional loss <=epsilon/p<=L. This uses the whole correlated joint law,
not a product of private marginals or incompatible per-type solves. Tiny
posterior masses may produce huge finite horizons; no uniform mass floor exists.

cfrDFiniteChildProfile_isNash follows from that actual finite recurrence and
complete played/deviation-law preservation under public splicing.
cfrDFiniteChildProfile_referenceBudget reconstructs the actual typed game;
cfrDFiniteContinuation_leafOptimal includes constructed zero-own-reach responses.
cfrDConstructedFiniteOracle_accurate and _leafOptimal hold at every round of
the perturbed outer recurrence, not an independently supplied trace.
Its _isNash and _carried_security retain numerical error, child loss, and
finite outer regret separately: A*error+B/sqrt(T)+2*L. The only equilibrium
premise in carried security names the original-game comparison value, not
a child solution. Numerical error remains an explicit assumption about the
predictor, not a guarantee of neural training or floating-point execution.

The seven new compiled controls cover actual prefix-law preservation,
nonfactual public queries, no live game at zero remaining fuel, the constructed
all-query child contract, every actual outer iteration, numerical bias 1/8
with child tolerance 1/4, and full-game approximate Nash for that noisy instance.
The bias is not claimed to force every learning trace to change. Inherited
nonconstant-learning, no-global-mass-floor, seed/average, off-path, replacement
and negative controls remain intact and were rebuilt.

This is an adaptive real-valued complete-plan NORMAL-FORM reference, not the
paper's fixed-T information-set child CFR or an executable numeric refinement.
The remaining M06 construction is fresh recursive solving at actual carried
PBSs and its security transfer; privateCarriedContinue retains one selected
complete policy. Arbitrary independent replacement is still excluded by the
existing counterexamples. Do not manufacture a local safety certificate to
close this gap. Keep printed/corrected Theorem 3 and variant source claims apart.
M06-finite-child.md is the additive coverage journal; all four original M06
parent obligations remain pending, with no main integration or acceptance.
