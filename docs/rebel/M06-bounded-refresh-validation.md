# M06 bounded-refresh execution: validation and semantic boundary

This records a verified dependency slice for an explicitly named variant,
not acceptance of M06 or the paper-faithful recursive test-time guarantee.
Proof source: `ae60d4105b67c478c23d594bca4cd7587c140ecb`.
Source branch: `rebel/m06-bounded-refresh-20260921`.
Restart/evidence branch: `rebel/m06-refresh-checkpoint-20260921`.
The evidence checkpoint changes no Lean source, dependencies or validation gates.

## Restart continuity and saved stages

The actual starting checkpoint was a39599e3b47b1e50ca78d5a6385aa24035d25738,
which already contained the finite-child repair f4671e42. The old d6db5e46
inference failure was not replayed. Main stayed at
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. All five changes are descendants;
no force update, history rewrite or main integration was performed.

| Commit | Saved stage |
|---|---|
| 5071dff746e9d7c04a27849e85391b7d1b749f56 | Record the validated inherited base and the bounded-refresh construction plan. |
| a4b6e1300b6c0f3c5bba9cacc850c84a787d5591 | Add the carried-step expectation identity and private mixture loss bound as a compiler checkpoint. |
| 082cc8780095ef062cb652b9797b148f9d546c5c | Add actual finite carried-PBS candidates, recursive schedules, security, controls and all registrations. |
| e3dab69dfba0d4d20c1d780d4884d1094b263cbc | Eliminate the stopped decision before reducing its dependent instance. All three general modules compiled. |
| ae60d4105b67c478c23d594bca4cd7587c140ecb | Repair the missing-model retention control by direct definitional reduction and mix_self. |

The inherited STATUS is preserved byte-for-byte in
M06-status-before-bounded-refresh.md, blob 3777ef9dd241c44c0f21d8a6cd4c2a0bb2e7667d.

## Exact-source verification actually inspected

Target run `35535271115`, job `106143057959`: SUCCESS in all steps.
All 65 declared M06 targets built (3,320 Lake jobs). The supplemental build
reports 3,310 jobs. The unchanged supplemental audit logic, expanded by four
module names, inspected all 292 complete transitive declaration records in
27 modules. All 27 normal/slow module lint passes are present. The downloaded
log contains no error: or warning: records and ends with
`EXACT_LEAF_VALIDATION_PASS modules=27`.

The four new modules account for 49 records (12, 22, 1 and 14 respectively),
including compiler-generated equations, private helpers and local instances.
The source itself adds 12 general theorems and seven example theorems. These
counts are not interchangeable and are not a framework completion percentage.
Every inspected axiom set is a subset of propext, Classical.choice, Quot.sound.
M06-bounded-refresh-axioms.txt contains a labelled normalized 49-record excerpt.

Artifact: `10612846238`, m06-targeted-ae60d4105b67c478c23d594bca4cd7587c140ecb.
ZIP SHA256: `08e12d7a226ae2f1e867e47719781b06a270957280a1b150df56e7d34d6a9ec2`.
Complete raw-log SHA256: `1848e52b1b0b0806b8ff12541d5eae7abf5631abf28ae459d79d432345c92a81`.
Pinned toolchain: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

| Same proof source | Run / job | Observed state at evidence recording |
|---|---|---|
| Source inventory | 35535271079 / 106143057820 | Success |
| Full repository build/lint/architecture | 35535271071 / 106143096344 | In progress; not claimed successful |
| Full ReBeL compiler/lint/transitive axioms | 35535271126 / 106143099577 | In progress; not claimed successful |

The full ReBeL job's width, static architecture, ledger/inventory/fixture and
independent rational-runtime steps passed, but intermediate steps do not count
as final full-workflow success. The new documentation head has its own runs.

## Failures and repairs

Run 35534241817/job 106140278761 at a4b6e130 rejected an underspecified scalar
in the nonnegative stopped-branch proof and unused simplifier arguments.
The next source made the scalar explicit. Run 35534683349/job 106141469146
at 082cc878 then exposed an instance-transparency mismatch: reducing the stage
fuel before rewriting the dependent decision left an ill-typed rewrite motive.
e3dab69d first eliminates that exact stopped decision and then simplifies.

Run 35534933447/job 106142145109 at e3dab69d compiled all three general modules,
including the concrete recursive security theorem. Its only remaining error
was the missing-belief example's simplifier failing to instantiate a dependent
candidate lemma. ae60d410 applies the existing mix_self theorem directly.
No statement, premise, axiom allowlist or linter was weakened for these repairs.

## Source integrity and offline checks

The e3dab69d source snapshot is artifact 10612004728 from run 35534933507.
ZIP SHA256: `27ad001d9b569d5905151ad624de529ecc72dc8a012a6fe7b31f45869e9c59e8`.
Its source-commit marker and all seven changed code/registration/audit files
were inspected. The plugin-confirmed ae60d410 commit has e3dab69d as its sole
parent and changes exactly one proof line in one example file. Applying that
one-line difference to the exact snapshot reproduces blob
5c22600ac5714503914080ed2610db9f028ef89e and the final source tested offline.
This is a verified reconstruction, not an independently downloaded ae60 archive.

All 76 existing Python tests passed with warnings as errors on that source.
Coverage and inventory structural checks passed with 3,054 expanded rows intact:
64 verified, 41 qualified, five refuted, 406 context-indexed, one empirical,
2,537 pending. All 503 non-Experimental Lean files satisfy the 100-column limit.
The full audit enumerates 177 modules; enumeration alone is not a full audit.
The umbrella, target list and supplemental auditor differ from the base only
by four added module entries. No inherited source, target, test or dependency
pin was removed. coverage.json and the global axiom auditor are unchanged.
Offline processing used plugin-downloaded content, without local git operations.

| New source | Git blob | SHA256 |
|---|---|---|
| CFRDRefreshMix | 5c5a7db1ca718c1c4b43f9163bddbc6f0304b8e3 | 649c0024b9f077b18f3c4321fdf463fac48b0f259b941efbc29d5d76984cc925 |
| CFRDFiniteRefresh | ae44776c12a05f620c53e9bc3d6295c04ef8d091 | 18294f87583be35d528570a59482ffabb7977fbd69939cadbe0f44c0491c1862 |
| CFRDFiniteRefreshSafety | bc3ea6057cabf5a986a4623ca2d24ac0e05be2a6 | 39416c642fe15fadba4e5e0ccce1895cfe656e60334f951362f4359a26159990 |
| Examples/CFRDFiniteRefresh | 5c22600ac5714503914080ed2610db9f028ef89e | f14f3157bed523aee1e9afb15bc50ba54ae81736bfb32b6adb20822128a43a56 |

The base a39599e3 full CI 35518435920/106098224758, full ReBeL
35518435948/106098224868, and inventory 35518435989/106098225132 all succeeded.
Its downloaded ReBeL output contains 173 module lint passes and 3,544 axiom
records. This is inherited validation, not validation of a changed descendant.
Base source ZIP SHA256: 602b707694ec4d70c79824a6f4661710d02cf80b4a292d1851fd629540e8e058.
Base validation ZIP SHA256: 089162ce171f8e6d11e07ee657d255c0192dcefdd752943cde9c51bd2ef7a492.

## Constructed semantics and derived bound

Each live stage's resolver receives only retained private memory, public
observations and the optional carried MODEL joint PBS. It receives neither
the actual hidden history nor the unknown opponent's strategy. On a present
PBS it computes the existing finite normal-form regret-matching candidate at
that posterior's mass budget, solving the whole remaining horizon. It executes
only the current stage fuel before the next query and posterior update.

One private profile draw chooses that candidate with probability r in [0,1]
and otherwise retains the CURRENT complete memory profile. This is not an
independent mixture at each action. Canonical memory and carriedBeliefUpdate
retain the chosen model and update its joint PBS. The model PBS is not assumed
equal to the unknown opponent's true posterior. Missing support retains the
current profile; terminal and zero-fuel stages use the existing no-query rule.

CFRDRefreshMix composes an actual carriedMemoryStep with its selected-policy
tail. Under |u|<=B, the old and fresh continuation values both lie in [-B,B].
The private mixture's loss is r*(old-new)<=2*B*r. This is pointwise at every
carried state, including off-model histories. CFRDFiniteRefresh therefore
constructs all CarriedResolveStepBounds on the actual forward state laws and
composes a finite schedule, charging at most stageCount*2*B*r. Stopped stages
are conservatively counted even though they incur no actual replacement loss.

The concrete theorem cfrDConstructedFiniteOracle_refreshed_security supplies
the prior bound from the actual noisy outer finite-child CFR-D recurrence:

    V_ref - (A*predictionError + C/sqrt(T) + 2*childLoss)
          - stageCount*2*payoffBound*refreshRate <= refreshedExpectedPayoff.

The original-game comparison equilibrium only names V_ref. No child Nash,
posterior mass floor, local replacement inequality or recursive safety
certificate is assumed. Finite histories/actions, full-AOH recall, two-player
zero-sum bounded utility, positive child tolerance and T>0 remain explicit.
The numerical error bound is not a theorem about arbitrary trained networks.
Zero prediction error does not remove the finite-T term.

For each present PBS, the candidate's approximate Nash property is separately
proved against all behavioral deviations. The retain-old mixture is NOT
asserted to have that same Nash budget. The replacement-cost proof does not
use candidate Nash and remains valid for a poor legal candidate. These are
different guarantees, not a circular justification of one by the other.

## Hostile controls, coverage and remaining work

In the same canonical carriedMemoryStep execution, refreshing fair play toward
a bad constant policy has loss exactly r; at r=1/4 the loss is positive. That
bad resolver is a control of the general mixture, not the finite solver's
claimed output. Other controls cover arbitrary existing memory with a missing
PBS, a genuine live finite candidate, zero fuel, and two-stage fuel/forward
comparison identities. Existing independent-Nash replacement counterexamples
remain. Supplementary rational endpoint and two-stage branching enumerations
also passed; these arithmetic checks are not substitutes for Lean proofs.

This is an explicitly named BOUNDED-REFRESH VARIANT. Large rates or many stages
can make the additional penalty vacuous. It does not prove that arbitrary
independent re-solving is lossless, or that the new penalty can be removed.
The finite child remains an adaptive real-arithmetic complete-plan normal-form
reference, not fixed-T information-set CFR or a numerical executable refinement.

The unmodified paper test-time variant still needs its own counterfactual or
global-security proof and exact source correspondence. Do not relabel this
bounded variant as that result. The next original-variant task is to construct
and verify the source-faithful recursive solver/value-envelope guarantee,
rather than assume old/new Nash implies fixed-opponent value preservation.

Coverage journal: SEARCH-CFRD gains actual carried-PBS re-solving for this
explicit variant; SEARCH-ERROR gains derived recursive replacement allowances.
Original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. No original source row is promoted or deleted. M06 is not accepted.
