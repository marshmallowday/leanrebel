# M06 opponent-uniform source-law rates

## Checkpoint and scope

This implementation continues repair source
8a82e7fdee7cd7fc23c1b40609ab7c869750939e on a separate branch,
rebel/m06-uniform-source-rates-20260924. The repair branch, failed predecessor,
all accepted slices and main are preserved. No main integration is requested.
All remote reads, writes and Git operations use the ChatGPT GitHub plugin.

The repair passed M06 target run36003811993/job107646728317, including
131 targets and supplemental normal/slow lint and transitive axiom audit:
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1474;
EXACT_LEAF_VALIDATION_PASS modules=93. Inventory36003811987 also passed.
Full CI36003811808/job107646730056 is now SUCCESS, including whole-library
build/lint, architecture Phases1/2/3 and tracked-file cleanliness.
Independent ReBeL36003811764/job107646727800 is still being checked; its
exact-source snapshot107646727703 passed. These are evidence for the repair,
not acceptance of this new extension.

## New mathematical slice — pending compiler acceptance

DominatingReachBound defines a finite structural cap D by summing inverses of
uniform legal own reach over legal histories. The denominator is positive by
uniformInformationReach_positive, even on histories that have zero probability
under current play. Every unknown behavioral opponent's information-local
density is at most D because its own reach is at most one. The cap does NOT
assume a minimum positive current PBS/query probability. Finiteness of the whole
legal history carrier and finite local menus are explicit. This is a conservative
real-valued proof bound, not a numerical executable or a sharp complexity bound.

CFRDUniformSourceRates bounds the actual source cost by

    loss + B * outcomeRate + 4 * B * D * referenceRate.

The first radius bounds actual continuation-outcome L1 differences at histories;
the second bounds unnormalized reference-atom L1 differences. The theorem then
integrates the SAME private parent seed. It is uniform over arbitrary unknown
opponents. No desired root security inequality, resolver envelope, current query
mass floor, or identification of actual and model posterior is assumed.

The actual HiddenTypes fresh-chain consumer discharges referenceRate=0 by the
previously constructed chain's exact reference-law preservation. It retains
outcomeRate as a source-law premise, obtaining 1/8 + 2*outcomeRate. A separate
unconditional control uses the universal L1 bound two, giving33/8. That constant
is deliberately NOT called a vanishing rate or a useful final security estimate.
All inherited rare-query, NEW-only atom, disappearing-query, absent-OLD-query,
zero-fuel, seed-coupling, finite-parent and positive-bias controls remain present.

## Integration and remaining obligations

All three new modules are appended to the analytic root, M06 target list and
supplemental audit. The131 prior targets and93 prior audit modules remain in
order; new totals are134 and96. No warning gate, workflow, architecture check,
dependency pin or axiom whitelist is weakened. The only allowed axioms remain
propext, Classical.choice and Quot.sound.

Source locator: SAFE-THEOREM3, main section6/p8 Theorem3 and supplementG
pp.21-22; SEARCH-ERROR additionally tracks appendicesG/I and cited CFR-D and
DeepStack results. This is a qualified source-law bridge, not a proof of the
unmodified paper theorem. Neither independent Nash quality nor scalar oracle
accuracy is asserted to imply a small outcome radius. Deriving shrinking radii
for the intended algorithm, useful native first-exit rates, independent solves
at later carried PBSs and CarriedResolveStepBounds remain open. The printed and
corrected finite-T Theorem3 forms remain distinct, with finite parent error
retained even at zero prediction error. M06 parent coverage statuses stay pending.

## Initial compiler failure and scope repair

Initial extension source2264eefd5c25f99b606e9c83ca94e5f536a3d8d9 failed M06
run36005895147/job107653834466 on2026-09-24T13:34:09Z. The exact target artifact
is10810825855, SHA256
36a1c95c76208401bd30a49e63e004559a24c0736d318a69e72f5fa15689221e.
The compiler reports only unusedSectionVars in DominatingReachBound:
[Fintype player] and [DecidableEq player] at unilateralDensityCap_nonneg,
and [Fintype player] at unilateralDensity_le_cap. Proof bodies elaborated,
but the warning-as-error gate correctly failed; downstream new modules and
supplemental lint/axioms were not accepted.

The repair removes the unused finite-player instance and scopes DecidableEq
only before the ratio theorem that needs it. It does not disable a linter or
alter a proof body, mathematical conclusion, target, import, gate or whitelist.
The tighter hypotheses strengthen the API instead of suppressing the warning.
The initial failure remains in branch ancestry. Inventory36005895166 passed.
FullCI36005895266 and independent ReBeL36005895063 belong to the failed initial
source, not to the repair; inspect exact repair-SHA results before acceptance.

## Validation to record

Read exact repair-SHA target, full CI, independent ReBeL and inventory results.
On any failure inspect compiler/normal-slow-lint/transitive-axiom logs and repair
without dropping declarations or targets. Record run/job IDs and artifact
hashes before marking this slice accepted. No new theorem in this document is
claimed compiler-verified at this checkpoint. Local checks of the exact initial
source passed76 Python tests and the coverage/inventory structure checks; those
are not substitutes for Lean compiler and axiom acceptance.
