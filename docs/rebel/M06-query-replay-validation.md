# M06 same-setting replay — compiler and semantic checkpoints

## Lineage and preserved work

Start: 2e1de273b9164743decdd8a283b3249f34bf5600 above the accepted
4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5 value-coupling source.
Independent predecessor ReBeL run36103763078/job107971751432 succeeded;
see M06-signed-query-progress.md for inspected log counts and artifact hashes.
Initial resumption commit: fa4d71e14706718ecde9f680b8d87923c821343a.
Core replay source: 2973770a358ef63c94ada29a3d52d1f33f16d164 on
rebel/m06-signed-query-20260925. Its M06 run36108618063/job107986765815
compiled all135 targets and was still in supplemental lint/axiom validation
when this record was assembled. Do not count an unfinished audit as success.
That branch is left fixed; the consumer is on rebel/m06-query-replay-20260925.

## Dependency-closed implementation

CFRDQueryReplay proves that the actual finite information-CFR child table
depends on its complete joint cut law, not a tuple of public marginals. Equal
prefix decisions preserve the table, child profile, computed off-path response,
retained native child queries and the continuation of each actual noisy parent
round. These equalities hold with the SAME fallback/payoff/cut/horizon/bound/
loss setting. They do not assert equality of different solver budgets.

CFRDQueryReplaySafety proves zero positive supported-query drift for one such
recomputation, uniformly over actual parent rounds. It also transfers the
fresh child's coherent private-plan draw through the original actual private
seed/history distribution. Early terminals and arbitrary seed-blind unknown
opponents remain covered. The resulting root security bound retains prediction
error, the finite-T term and2*childLoss; it assumes no stability certificate.

The final draw in the actual-law/security result is the existing coherent
private-plan realization, NOT the native per-child iteration draw. Native
retained-query sampling has its own supported conditional-law equality.
Off-model public observations do not receive a fabricated posterior. This
fixed-cut same-setting result does not close later carried-PBS/native-first-exit
obligations or establish a rate for changing child tolerances.

## Positive and hostile controls

The real hidden-type noisy parent retains bias1/8, loss1/4, every finite round,
both players, arbitrary parent weights and a fixed unknown opponent. A genuine
reference-supported but factually absent query exercises native query replay.
The negative control has nondegenerate identical observation marginals but
conditional expected payoff difference1. Zero execution fuel bypasses draws.

## Static checks and a preserved integration failure

The initial offline76-test run on the developing three-module tree failed two
public-umbrella registration checks. Registering the three imports (without
removing or changing the tests) fixed both; the repeated76-test run under
-W error passed. Expanded ledger/inventory checks pass for3054 entries.
The early source297377 intentionally preceded public umbrella integration and
must not be represented as having passed all repository integration gates.

The final target and supplemental audit lists contain137 and99 entries,
respectively; every inherited entry is retained. Strict public/private/generated
transitive axioms are still limited to propext, Classical.choice and Quot.sound.
No workflow, timeout, warning policy, dependency pin or negative test is weakened.
All source lines satisfy the existing100 UTF-16-code-unit limit. Local checking
uses plugin-downloaded source with no Git commands or remote GitHub requests.

The source blobs were independently computed offline and checked against the
GitHub plugin responses. Compiler/lint/axiom and full-CI results for the complete
slice must be appended with their exact source SHA and run/job IDs before
acceptance. Parent coverage statuses remain pending; M06 is NOT complete.
