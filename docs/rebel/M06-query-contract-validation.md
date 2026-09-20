# M06 query-contract checkpoint: validation and semantic scope

This records a compiled intermediate proof, not acceptance of M06 or Theorem 3.

## Exact source and repository continuity

Proof source: `482ebe19486c92035f395fee92acf2bd49ab183c`.
Its source branch is `rebel/m06-joint-completion-20260920`.
The restart/evidence branch is `rebel/m06-contract-checkpoint-20260920`, whose
initial change after this source is documentation only. Separate branches keep
the source's running verification jobs alive while recording their status.

At restart, `cd2f5be3a19ec6774037636070a9478f24cf2676` already contained the
parallel `b5978ef674f46f02c4b39785b033dd42bdc26ddf` work (five commits ahead,
zero behind). It was not merged or duplicated again. Main stayed at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. All six implementation/repair
commits below are descendants, without force-updates or history rewriting.

| Commit | Change |
|---|---|
| `943964003e6ae661af85fd3a1a03b5e9493b1527` | Use the actual `conditionalOracleValue` definition in the inherited query theorem. |
| `da4c6170c949a5e52a8e9895e0b7e037ac285544` | Add the six query-contract theorems, register them, and correct the stale restart record. |
| `61b417868c55851d2c46885e7fd7367c571e7ca3` | Add five canonical live/zero-reach query controls, retaining every inherited control. |
| `9d4ec617c814ef82044ab88f779560b68773538e` | Scope finite-menu assumptions to the lemmas that actually need them. |
| `694534d261ee74ba8704ddcf330a08ee159629e8` | Wrap two test statements to satisfy the unchanged 100-column limit. |
| `482ebe19486c92035f395fee92acf2bd49ab183c` | Beta-reduce the mapped observation equality before rewriting in the factual-zero test. |

The original STATUS was archived with the identical blob
`8a9fd396bf24b6dc9ecd88aa97aaa8de85d1280d`, preserving accepted M00-M05 evidence.

## Compiler evidence

Target command: `lake build $(cat scripts/rebel/m06-targets.txt)` after fetching
the pinned dependency closure. Toolchain: Lean 4.33.1,
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Exact-source run `35482474735`, retry job `106002870720`: SUCCESS.
All 35 declared targets built; final output: `Build completed successfully (3278 jobs).`
The downloaded compiler log has no `error:` or `warning:` records.

- Artifact ID: `10595974726`.
- Artifact name: `m06-targeted-482ebe19486c92035f395fee92acf2bd49ab183c`.
- Artifact ZIP SHA-256: `a2307a6d84a4cd8c14404639803913fe23911550a09f1fc8254bed964e349fb9`.
- Raw full compiler-log SHA-256: `bbff8057c2508e64921d277a457ca815ce6eac0f39fb53b803e8ae56d2e53b0f`.

[M06-query-contract-compiler.txt](M06-query-contract-compiler.txt) preserves a
labelled exact excerpt, not a file claimed to have the raw full-log hash.
The workflow log is at
https://github.com/marshmallowday/leanrebel/actions/runs/35482474735/job/106002870720 .

## Observed failures and repairs

The inherited `cd2f5be3` run `35480034249`, job `105996070767`, failed on nonexistent
`conditionalOracle` / `conditionalOracle_eq` identifiers. Repair `94396400`
passed target run `35481397559`, job `105999754058`.

The new `da4c6170` target run `35481685338`, job `106000529025`, exposed an unused
section finite-menu assumption. The repair scoped the assumption properly; no
lint was disabled. At `694534d2`, the new six-theorem module built successfully,
but target run `35482197682`, job `106001920553`, rejected a beta-unreduced
observation equality in one test. Repair `482ebe19` preserves that test's statement.

The first `482ebe19` target job `106002635153` failed BEFORE compilation while
Elan's installer download reported an SSL connection reset. The GitHub plugin
reran that job at the same source; job `106002870720` then passed. No action pin,
dependency, source, or gate was changed in response to the network failure.

## Other checks at the recording checkpoint

| Exact source | Gate | Run / job | Observed state |
|---|---|---|---|
| `482ebe19` | ReBeL compiler, normal/slow lint, transitive axioms | `35482474752` / `106002668307` | Running; final success and axiom output not yet inspected. |
| `482ebe19` | Full repository build, lint, architecture audits | `35482474749` / `106002665821` | Running; not accepted as passed. |

In the ReBeL job, line width, static architecture, ledger/inventory/adversarial
fixtures, and rational Lean runtime with independent response checks already
passed. These are intermediate steps, not completed full workflows.

An offline archive review matched the changed source blobs below, ran all 76
existing Python tests successfully, passed ledger/inventory structure checks,
and found zero UTF-16-width violations over 100 columns. The unchanged ledger
contains 3,054 items: 64 verified, 41 qualified, five refuted, 406 context-indexed,
one empirical record, and 2,537 pending. These are NOT a completion percentage.
Static enumeration puts both changed proof modules in the 148-module ReBeL audit
closure; enumeration alone is not a successful compiler or axiom audit.

| File | Git blob | SHA-256 |
|---|---|---|
| `CFRDConditionalCompletion.lean` | `b4342b750f822c839dde748aad1f7973db2019fb` | `57c3d6b26bf779fbce7cbd4626dce25c8cac8db05118ce86c6cdf31ca9c0ea2e` |
| `CFRDCompletedContract.lean` | `20ee2fb2baf63195e96e16f7c8d350acb66b8438` | `88f8420e5183ced78ad80617f21924a49f030d2800edd419daefa4d40a4d92b0` |
| `Examples/CFRDZeroReachControl.lean` | `58833dd2d01d84bc4f41585cb3c0b18c3333dbfa` | `59d44ec56d32906324301dd1e7cb4d6853316735ec25c227012d1e78679c61f0` |
| `scripts/rebel/m06-targets.txt` | `1601fb755da077ad02a0ea99f2a06b3ab367c72d` | `dba19ccb012c226cfc21593073d2f9f0f4ce054f7a6c6b21246106742541add9` |

## What the controls establish

The new Lean controls are `zeroControl_query_packet`,
`zeroControl_reference_supported`, `zeroControl_factual_info_absent`,
`zeroControl_reference_deviation_value`, and `zeroControl_opponent_not_reference`.
They distinguish factual zero reach, genuine reference support, and exclusion by
an opponent. Policies remain full information-local behavioral policies.

An auxiliary exact-rational calculation using the existing independent
`rational_reference.py` semantics checked unchanged terminal laws against all
1,024 pure opposing policies for each player (2,048 cases total). In this fixture,
the focal zero-own-reach history has factual probability zero and reference
probability 1/8. The opponent-excluded history has reference probability zero.
The individual-history continuation changes from -2 to 0, while its full private-
information-conditioned mean stays -1. Do not cite that pointwise change as a
strict information-conditioned improvement. These numerical observations are
supplementary evidence, not kernel-checked theorems or a substitute for axiom review.

## Semantic acceptance boundary

The six new theorems are documented in [M06-completed-contract.md](M06-completed-contract.md).
They prove the completed solver leaf contract CONDITIONALLY on compatible
canonical query games and local implementation of computed finite responses.
They do not construct the final `queries` premise for recursive child solves.
In particular, neither ordinary on-policy Nash, equal initial outcome laws,
abstract numerical accuracy, nor an arbitrary equilibrium replacement supplies it.

The five controls validate the reference-law part of this bridge; they are not
a general instantiation of the final query-game premise. Construct the public-
state response splice, the typed query kernels and factual weights, then the
recursive child solver and finite-T continuation-loss propagation. Keep original
and corrected Theorem 3 separate and retain finite-T error at zero oracle error.

No original M06 parent row is promoted: `SEARCH-FRONTIER`, `SEARCH-CFRD`,
`SEARCH-ERROR`, and `SAFE-THEOREM3` retain their pending source obligations.
Only `propext`, `Classical.choice`, and `Quot.sound` remain allowed. No test,
trusted boundary, action pin, audit expectation, or dependency was relaxed.
