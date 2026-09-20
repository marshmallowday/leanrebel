# M06 conditional-loss bridge: verified slice and restart evidence

This records an intermediate dependency slice, NOT acceptance of M06.
Proof source: `af8b63282a49cdfb68df411e5527b6ba3e288d42`.
Proof branch: `rebel/m06-conditional-loss-20260920`.
Restart/evidence branch: `rebel/m06-conditional-checkpoint-20260920`.
The evidence commit changes documentation only. Read its actual remote HEAD;
do not reset to older recovery or driver branches.

## Saved stages

The entry checkpoint was `b5e15493d6efdc4fa641aeb690e40b24a0764d11`.
All four implementation/repair commits are descendants; no force update,
history rewrite, dependency change or main integration was performed.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.

| Commit | Change |
|---|---|
| `594cfc652882a61cf4c62beb1c47e1d0fc8a843c` | Add probability-weighted approximate PBS bounds and preserve the prior STATUS. |
| `d1903087f325931e954ad9efde9ef6389264bfd5` | Add approximate completed leaf contracts and canonical controls; repair the target-path typo. |
| `fed8cc06b6eb875397f057fee5639e1bb19bb80d` | Repair saturated conditional-mean rewriting and add finite-plan approximate Nash realization. |
| `af8b63282a49cdfb68df411e5527b6ba3e288d42` | Repair example proofs using the existing canonical epsilon-Nash API; preserve all example statements. |

The original STATUS is archived in M06-status-before-conditional-loss.md,
with identical Git blob `bba1393b0b6cccbaabf9dc6552ac612f023d720c`.

## Exact-source compiler, lint and axiom evidence

Run `35508389830`, job `106071929602`: SUCCESS on the proof source above.
Commands: `lake build $(cat scripts/rebel/m06-targets.txt)` and
`python3 scripts/rebel/audit_exact_leaf.py`.
Pinned toolchain remains Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

All 51 distinct declared targets exist and built: 3,306 Lake jobs.
The supplemental closure then built in 3,295 jobs. It inspected 113 complete
transitive declaration records in 13 modules, including private/generated
declarations, and ran every named module through normal/slow lint.
All 113 wrapped records were independently parsed and checked; no axiom
outside `propext`, `Classical.choice`, `Quot.sound` occurs. The raw log has
no `error:` or `warning:` records. The new three modules contribute 26 audited
declarations: five in PBSApproximateOptimality, three in CFRDApproximateLeaf,
and 18 (including generated declarations) in its example module.

Artifact ID: `10604568141`.
Artifact: `m06-targeted-af8b63282a49cdfb68df411e5527b6ba3e288d42`.
ZIP SHA256: `3052c70fa6f892cd46777e253db429c6f37fa0561e49fd6a5c09f1cea3c8df61`.
Full raw log SHA256: `798bccdb7621883cf9133f324633bd1a9d753cffcdf1a9f604bc420a60cfa8eb`.
M06-conditional-loss-axioms.txt is a LABELLED normalized excerpt of the 16 new
public theorem records, not a file claimed to have the full-log hash.

Source inventory `35508389752` / `106071929279`: SUCCESS on the same source.
Full CI `35508389747` / `106071929220` and full ReBeL
`35508389751` / `106071965121` remain running at this recording checkpoint.
Their final results must be read separately. The supplemental 13-module
success is not completion of the full 164-module ReBeL audit. The full ReBeL
job's width, static architecture, ledger/inventory/fixtures and rational Lean
runtime/independent-response steps have already succeeded.

## Earlier feedback and repairs

`594cfc65` failed `35507002570` / `106068402421` on redundant simplification,
addition orientation, and an erroneous Examples prefix on CFRDResolveBelief
in the target list. The real inherited target was restored, not removed.
`d1903087` failed `35507628947` / `106070005103` on a partially applied
conditionalPayoff in an expectation. Saturating the type argument and proving
the mean identity pointwise fixed it.
`fed8cc06`, run `35507973352` / `106070880347`, compiled both general modules
(all eight new general theorems), but its example proofs expanded the mixed
Nash goal too far and tried an inapplicable zero-error simplification.
`af8b6328` instead uses `isεNash_iff`, `isNash_iff_isεNash_zero`, and
`IsεNash.of_isNash`; it also removes an unused simplification argument.
No theorem type, negative control, allowed axiom, lint rule or frozen gate
was weakened in these compiler repairs.

## Inherited verification resolved

The entry source b5e15493 passed full ReBeL run `35503671838`, job
`106059741567`: 161 modules, 3,394 transitive declaration records. Every record
was read from artifact `10602644467` and checked against the same allowlist.
ZIP SHA256: `2569715f99adaec69c23fba2b4940309b23302d7e902d4f0cde06548a4b1ecfc`.
Raw validation-log SHA256:
`f03c70a560bfb77f774889bf8a9f6dcd53e4c4e235f251932ba0e9c83d835096`.
The earlier 0b6d3f36 full CI `35503252425` / `106058634035` succeeded, while
its ReBeL run `35503252397` was cancelled. The later exact-source success
is separate evidence, not a relabeling of that cancelled run.

## Source identity and offline checks

Exact-source snapshot: artifact `10604118066` from run `35508389751`.
Snapshot ZIP SHA256:
`3a76608417676e89f2118fc0689deecc079ae0b0d02e45e35a47114a3e9e97b3`.
The snapshot commit and tar digest were checked. All three new Lean files,
the analytic umbrella, target list, and supplemental auditor match the
working copies byte-for-byte. Offline work used only plugin-downloaded files.

On this exact snapshot, all 76 existing Python tests passed with warnings
as errors; coverage and inventory structure checks also passed. All 3,054
expanded original ledger rows remain intact: 64 verified, 41 qualified,
five refuted, 406 context-indexed, one empirical, and 2,537 pending. These
counts are not a completion percentage. All inherited imports and 48 targets
are retained; the three new targets are registered and distinct. No UTF-16
line width exceeds 100 in the 489 non-Experimental Lean sources. Toolchain,
lake-manifest.json, lakefile.lean and coverage.json are byte-unchanged.

| New source | Git blob | SHA256 |
|---|---|---|
| PBSApproximateOptimality | `2043c700043a0e0876b8119a5a57138c7b00d513` | `fc7832d107bfc8d6f9020b20e6f2ac9d466a9e0da089f3a52929c51d42aab936` |
| CFRDApproximateLeaf | `96f96a60ffe88bf7c26c56f003d28480f52397d8` | `67e2419e2094548d14a6c135baa1cdc2562c593c611da3dbaae5d6194c9d8ba3` |
| Examples/CFRDApproximateLeaf | `e46db82570aef4c14de5ffcf9b1343b8c88aeaed` | `c6c0c591c0d2100c8d5c988152ed885f44f298eda357511f7e1d35908dac156e` |

## Semantic review

PBSApproximateOptimality contains four conditional-loss theorems and the
finite-plan realization theorem. Canonical approximate PBS Nash bounds the
mean nonnegative conditional best-response gap because one legal remembered-
type splice simultaneously attains all conditional maxima. Hence a type of
mass p satisfies p*gap <= epsilon. A supported type has gain <= epsilon/p;
a root budget epsilon <= p*loss gives the requested conditional loss.
Zero mass is never divided away or treated as an off-path certificate.
`finiteBeliefForm_approxNash_realization` transports approximate mixed-plan
Nash into the actual behavioral PBS game with unchanged epsilon. Finite
predrawing covers every complete behavioral deviation, not just pure plans.

CFRDApproximateLeaf has three theorems connecting these budgets through joint
zero-own-reach completion, legal public-response splicing and the actual
reference table to `CFRDLeafOptimal ... loss`. Factual live queries use the
mass-budgeted approximate Nash premise. Nonfactual queries use the existing
constructed conditional best response at zero own reach. Reference support
supplies opponent positivity and the focal zero/nonzero case. No conditional
payoff inequality or final safety conclusion is inserted as a structure field.

The example module contains eight theorems. In the canonical finite zero-sum
type-plan matrix game, the baseline has root error p but type-zero gain one
for every 0<p<1; at p=0 it is exact root Nash with that omitted-type gain still
one. Deviations range over ALL mixed complete plans. The weight-simplex proof
establishes the probability interpretation for 0<=p<=1. The separate live
HiddenTypes example exercises the actual completed reference-table theorem
with its existing constructed exact child as the zero-error specialization.
It is NOT a positive nonzero-error finite-child-CFR implementation.
A supplementary rational enumeration of all four pure plans at p=0, 1/1000,
1/4, 1/2, 1 reproduces the root/type gap; it is not kernel proof evidence.

## Coverage and remaining construction

This slice advances SEARCH-ERROR and SEARCH-CFRD, but none of SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3 is promoted to completed here.
The instantiated finite-iteration child solver remains missing. Its output
must actually satisfy the factual approximate-Nash AND probability-budget
premises for the current query; existence or exact child Nash is not a
finite-iteration implementation. The new realization theorem supplies the
mixed-plan-to-behavioral step, not construction of the mixed-plan solver.

A concrete next step is a child solver at the actual finiteBeliefForm with
its own derived finite-iteration error, carried through
finiteBeliefForm_approxNash_realization and the mass budget. A single positive
mass floor cannot be assumed uniformly over arbitrary learned PBSs. Derive
budgets from each actual query or prove a sharper direct counterfactual bound;
keep any resulting adaptive-iteration variant distinct from the paper variant.
Fresh recursive re-solving at the actual carried PBSs remains a separate
construction and transfer proof. Preserve numerical prediction error, child
loss, optional replacement loss, outer finite-T error, and the printed versus
corrected Theorem 3 statements. No M06 or complete-framework acceptance.
