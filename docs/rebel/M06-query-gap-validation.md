# M06 query-gap targeted validation checkpoint

## Exact proof source and scope

Proof source: `5cf1369cf1e886650a90a4e027347dacf589d50b` on
`rebel/m06-query-gap-20260925`. Evidence checkpoint branch:
`rebel/m06-query-gap-checkpoint-20260925`. The checkpoint is documentation
only. All validation below identifies the proof source, not the checkpoint
commit and not main. M06 remains incomplete.

The semantic review is `M06-query-gap-review.md`; its statements that tests
were pending describe the implementation checkpoint before these results.
The current record is this file and `M06-query-gap-validation.json`.
No underlying source-paper parent is promoted to complete.

## Inspected compiler, linter and axiom results

Targeted run `36125907562`, compile job `108041849267`, completed SUCCESS.
The declared target build reports 3464 successful jobs. The exact-leaf audit
rebuild reports 3456 successful jobs, then `EXACT_LEAF_AXIOM_AUDIT_PASS
 declarations=1595` and `EXACT_LEAF_VALIDATION_PASS modules=100`.
All 100 configured module linter passes are present. In particular the
production conditional-value module has 12 audited declarations and the
example module has 23. Private and generated declarations are included.

The logs list successful checkType, defsWithUnderscore, deprecatedNoSince,
docBlame, impossibleInstance, nonClassInstance, simpComm, simpNF,
structureInType, subsetDotNotationLinter, synTaut, tacticDocs, unusedArguments
and unusedHavesSuffices checks for both changed modules. No new nolint entry,
disabled check, custom axiom, placeholder, removed target or weakened
statement was used. The complete transitive audit reported only the existing
allowance propext / Classical.choice / Quot.sound. The nine new theorem
axiom lists are retained in the JSON record.

Artifact `10860580985` was downloaded through the GitHub plugin and inspected.
ZIP SHA256:
`1c5c04f9895b452d42a6d52a2f504c7925f3c846d644a63c1cd5c6ec6d3cbbb5`.
The embedded log starts with the exact proof SHA; log SHA256:
`27468553a6962ab627a42888800f2d86eb614482467aedacc6cc3e552ee94f74`.

## Source and structural verification

Source artifact `10859427902` belongs to independent ReBeL run `36125907531`.
Its embedded commit and both archive hashes were checked. ZIP SHA256:
`08a7d0c356fc97eb353295b4b80af93df4021d6c7ed2705e54cd1c5d568f0bd9`.
TAR SHA256:
`4ea00aa90e61efe5e9ec05058feb4c104f956b09adbda035ede42eb34f295fd7`.

On that exact exported source, all 83 Python tests passed under warnings-as-
errors; coverage and inventory structure each checked 3054 ledger entries.
The UTF-16-width scan passed all 576 nonexperimental library Lean files.
The two modules occur in all four intended consumers. Global audit discovery
contains 245 modules; this is a structural count, not a global Lean pass.

Archive-to-archive comparison against parent fa03b39e found only the two Lean
files and three intended documentation files changed, with no deleted paths.
All prior theorem names remained. GitHub's independent comparison reports
109 added lines and zero deletions in the production module, and 84 added
lines and zero deletions in the example. The library umbrella, target list,
both audit scripts, Lean toolchain pin and dependency manifest are unchanged.

## Preserved repair evidence

Parent `fa03b39e497e4d9802d978caab052ce2802ccdc1` completed targeted run
`36124896554`, job `108038627933`, with 100 module linter passes and 1581
audited declarations. Artifact `10859582792` was independently downloaded;
ZIP SHA256 `e51ba5ba6644218826196d8199871fa0d5a65062f25e653e8596ed300a0318bf`,
log SHA256 `e8dc7f36cb082f4b90dda32700556da9450dc839d33ebc2cd870d6fe83d9dcba`.
Its exact source and complete conditional-value linter/axiom pass markers were
checked. This does not replace the separate successful 5cf1369c result above.
The failure of e58eff73 remains recorded in the implementation review.

## Pending integration and semantic obligations

At the last inspection on 2026-09-25, new-source ReBeL run `36125907531`,
job `108041928085`, and full-library CI run `36125907627`, job
`108041951383`, remained in progress. Parent ReBeL run `36124896574`, job
`108038645006`, also remained in progress. Source-inventory run
`36125907547` completed SUCCESS. The source branches were not moved to this
evidence commit, so their runs remain independently attributable.

Before main integration, re-check those exact-SHA global gates. The targeted
pass proves neither global CI success nor M06 completion. In particular the
new mean-gap results do not derive a native or late-training density cap,
change the opponents or slice, prove native first-exit, or supply
CarriedResolveStepBounds. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending. Full carried-PBS safety and the printed/corrected
Theorem 3 distinction remain intact.
