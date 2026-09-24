# M06 nested-depth exact-source validation

## Preserved budget repair

Source704e96ff6ed5b73b279191ea2d01629cc331e8d8 is retained on the separate
rebel/m06-depth-budget-integration-20260924 branch. M06 run35946360278,
job107465069923 has completed its declared-target compiler step successfully.
At inspection its supplemental lint/transitive-axiom step was still in progress;
that pending state is not an audit success. Its repository-wide checks remain
separate. This compiler success repairs the earlier e9d651b2 failure without
changing any accuracy premise, numerical value or recurrence.

## Initial nested candidate: rejected

Source22b15778ec0a8d6a50874176a4bd285665c46257 added the constructed nested
child/parent modules and their full build/audit coverage.
M06 run35946558196/job107465692425 failed compilation at
CFRDDepthChild.lean:207:90 because field notation was split immediately after
`.law.`. The later line247 diagnostic that a declaration uses sorry is the
compiler's recovery from that parse error, not a source-written proof placeholder.
The file contains no sorry/admit. The downstream driver/examples were not
accepted. Budget and inherited first-exit modules compiled successfully.

ReBeL run35946558227/job107465692283 rejected three lines of width101,101,104
before compilation. It did not run its full proof audit. Full CI35946558231
had no inspected final result. These failures must never be reported as passes.

## Repair and additional continuation control

The current descendant keeps `.law.positiveMassFloor` together and wraps exactly
the three offending lines. All child definitions, theorem statements and proof
steps are otherwise retained. The driver is unchanged. No limit, linter,
validation step, premise, test or source dependency is removed or weakened.
This descendant needs its own exact-SHA compiler/lint/axiom results.

The example module additionally instantiates parentCut1/childCut1/remaining1.
The parent cut is after chance; the child and its continuation each contain
one real decision. Its child perturbation is the positive half-allocation for
that1+1 root, and the outer bias1/8 and requested child loss1/4 are unchanged.
Both all-query completed child optimality and finite-T full-game all-deviation
Nash are checked for this split. The earlier2+1+0 split is retained: it has
one real parent and one real child decision, with terminal final suffix.
Neither test claims three real decisions in this two-decision protocol.

## Acceptance and scope

Inspect the actual HEAD of rebel/m06-nested-depth-20260924 and its exact runs.
Both root imports and the M06 target/exact-audit consumer lists retain every
prior entry plus all three nested modules. The audit enumerates owned private
and public declarations transitively and retains the original axiom whitelist.
The independent repository-wide checks are still required.

The candidate constructs one more nesting step; it does not yet establish
arbitrary-depth recursion, independent repeated re-solving safety, useful
source-level model-value/first-exit budgets, or CarriedResolveStepBounds.
All original coverage rows remain pending. See M06-nested-depth.md and STATUS.md.
