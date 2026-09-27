# 461 target result: stopped-state simplification repair

Source: `461a926c198d0801ab659b4d1773ded7fd6fd5f8`.
Target run 36281256829 / job 108513412501 failed at 2026-09-27T00:07:48Z.
The GitHub plugin downloaded the complete target artifact 10918699965.
ZIP SHA-256: `4eac9d07e82bc80310e3590056c1686e712ce6e579a9efa3679f9b764a92c09c`.
The complete m06-targeted.log has 22,044 bytes and SHA-256
`88465d1cc85cf9e458fd2b5bd8102525973e58ca64075c199d2b44ec18695e6b`.
It records exactly this source and the unchanged pinned toolchain.

The single reported compiler error was PBSOpponentModelTransport.lean:335:2.
In the stopped negative branch, simplification turned nonexistence of a
supported posterior into a universally quantified implication, leaving an
unsolved conditional on the original existential. This is a proof-script
failure, not a counterexample to the support bound. The previous unnormalized
propositional bound had compiled on 63aa, before the authored transport budget
was repaired. The example module could not be built after this core failure;
there is no accepted axiom/lint result for the complete 461 slice.

The current repair proves the Boolean-indicator inequality separately by cases
on `carriedStateSupported M state`, then uses it directly by native definitional
equality. It introduces no authored transport step, changes no statement,
premise, stopping behavior or probability law, and leaves all frozen gates
intact. The explicit bind-identity and unused-simp fixes from 461 are retained.
The repaired source requires its own complete compiler, lint and axiom output.

## Other exact-source observations

461 global run 36281256762 / job 108513599400 passed its line-width, frozen
architecture, dependency-closure and ledger/inventory/fixture steps. Its rational
runtime step was in progress and its global compiler/lint/axiom step had not
started at that inspection. No global success is asserted; a same-branch repair
may cancel unfinished prior runs. The source snapshot job 108513599793 succeeded.

Snapshot artifact 10918183690 was downloaded through the GitHub plugin.
Its ZIP SHA-256 is `2dd45e75db334c7c9f862fb23b00b3be47b23838b810083906cedc113f317b5a`;
its source-commit marker is exactly 461. Both proof files match the intended
blob identities, and all original core declarations/proof text are preserved
except the stronger import and new appended declarations. The new example
module retains all original lines. Pins, architecture/workflow gates, coverage,
umbrella, target list and axiom consumers are unchanged byte-for-byte.

The exact 461 snapshot passed all 120 Python tests locally with
`python -W error -m unittest discover -s scripts/rebel/tests -v`.
The resulting local log SHA-256 is
`54c4749c58d15803a137f424afe054fcd7cddb35aed08ffea79a295fa1ac5429`.
These are arithmetic fixture checks, not Lean validation. Source inventory run
36281256776 / job 108513373102 succeeded. Full CI run 36281256752 / job
108513540620 was still in its Lean action. M06 and all four pending source
obligations remain incomplete; the baseline b833 global pass is not reused.
