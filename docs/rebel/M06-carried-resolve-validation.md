# M06 carried-PBS resolver: exact-source validation checkpoint

## Scope

This records inspected compiler evidence for the fresh carried information-set
solver and the missing-model recursive-law slice. It does not accept full M06
or the original unrestricted recursive safety statement. Exact assumptions,
nontrivial controls, and the still-open supported-PBS obligation are in
`M06-carried-resolve-review.md`.

All repository access and commits used the GitHub plugin. Compilation and
lint ran in the fork's GitHub Actions, not by treating file editing as proof.
Main remains accepted M05; no dependency pin, linter, test, source coverage
row, or axiom allowlist was weakened.

## Successful theorem-source checkpoint

Source commit: `e83ad7db3ab6cfb9374a2d3faad8c53d6213ee7b`.
Source tree: `30468df072c1cb3a2c546ab0deb6926f26166715`.
Preserved branch: `rebel/m06-carried-resolve-20260923`.

M06 targeted proof feedback run `35823903393`, job `107061395827`: SUCCESS.
Both the declared-target build and the supplemental exact-child proof
validation step succeeded. The full job log was read through the GitHub
plugin, including the new declarations' axiom output and normal/slow lint.

Evidence:
https://github.com/marshmallowday/leanrebel/actions/runs/35823903393/job/107061395827

Observed commands and markers:

```text
lake build $(cat scripts/rebel/m06-targets.txt)
python3 scripts/rebel/audit_exact_leaf.py
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=2335
EXACT_LEAF_VALIDATION_PASS modules=62
```

The target build reported 3426 jobs, and the supplemental build reported
3405 jobs. The audit included all 62 named supplemental modules. Every
transitive axiom set was contained in `[propext, Classical.choice, Quot.sound]`.
Normal Batteries linters and the separately reported slow simpNF lint passed.
Warnings remain errors. These counts describe the inspected audit surface,
not a source-obligation completion percentage.

The four new modules were all compiled and individually linted/audited:

| Module under `GameTheory.Analysis.ReBeL` | Audited declarations |
| --- | ---: |
| `CFRDInformationResolve` | 29 |
| `CFRDInformationResolveRecursion` | 10 |
| `Examples.CFRDInformationResolve` | 10 |
| `Examples.CFRDInformationMissingModel` | 9 |

Counts include definitions, instances, and generated declarations, not only
public theorems. `cfrDInformationResolveStages_run_none` proves the complete
finite missing-PBS law. `missingModel_state_reached`, `missingModel_state_none`,
and `missingModel_state_live` establish actual reachability, model absence,
and a live continuation separately; `missingModel_recursive_law` applies the
whole-schedule theorem to that reached state.

The diagnostic artifact is named
`m06-targeted-e83ad7db3ab6cfb9374a2d3faad8c53d6213ee7b` under the same run.
For durable verification, identify the exact run, job, source SHA and markers
above; an expiring artifact is not a substitute for those identifiers.

## Integration repair and its separate evidence

Integration commit: `e7360412dacd76216823b1fa28702b84c1b4ae4c`.
Integration tree: `a43fffe0bc81be9666eeb4d0fc651f65a909a26b`.
Preserved branch: `rebel/m06-carried-integration-20260923`.

The plugin's commit comparison confirms that its only changes from e83ad7db
are four added direct imports in `GameTheory/Analysis/ReBeL.lean`, the semantic
review document, and STATUS. The four theorem/control modules and supplemental
audit script are byte-identical to the successfully tested source checkpoint.

The direct imports repair the existing proof-surface registration test. At
e83ad7db, ReBeL run `35823903390`, job `107061395668`, stopped at
`test_analysis_umbrella_does_not_hide_candidate_theorems`: Search already
provided a transitive build path, but the explicit analytic root was missing
the new four modules. The test was retained and the root was corrected.

For e7360412, the latest inspected results are:

- Source inventory run `35824538883`: SUCCESS.
- ReBeL run `35824538878`, job `107063312144`: line widths, static architecture,
  ledger/inventory/adversarial fixtures including the repaired registration
  test, and rational runtime all SUCCESS. The repository-wide compiler/lint/
  transitive-axiom step was still IN PROGRESS at the checkpoint read.
- Full CI run `35824538900`: IN PROGRESS at the checkpoint read.

These last two runs are not recorded as successful full integration. Re-read
these exact runs and the actual current branch HEAD before integration. A
separate documentation-only branch preserves the running integration branch
rather than superseding its source by another push to that same ref.

## Earlier failures and repairs remain traceable

`eb59ccf754862f1e584deeee4eb3a44df39cce60`, targeted run `35822279205`, job
`107056486306`: missing direct import of the existing stopped-run lemma and
an unreduced resolver match. Repaired without changing theorem statements.

`2b1d8c7d2daac51a36f46eb079c017e514d8766e`, targeted run `35823272134`, job
`107059492921`: the core resolver compiled; a recursive case indentation and
the order of the additive Nash allowance required correction. e83ad7db
contains those repairs and passes the targeted build/lint/axiom loop.

The earlier sampled-value parent checkpoint
`e630e689df13eddedafbe3c88c2bf12561b8d1a6` separately passed full ReBeL run
`35820699300`, job `107051833911`. That older success is not attributed to
the new integration SHA.

## Resume obligation

The fresh resolver and missing-PBS completion are implemented and the scoped
proof bodies above have compiler/lint/kernel-axiom evidence. Fresh solving at
an available stored PBS still needs a derived counterfactual opponent-value
upper envelope under changed actual carried-state laws, including actual
histories outside a present model law's support. A model-root sample identity
or caller-supplied `CarriedResolveStepBounds` does not discharge that obligation.

Keep the nonzero numerical error, finite outer-T term, positive child loss,
and printed/corrected Theorem 3 distinction. Missing-PBS zero additional loss
is not individual-iterate safety and is not full recursive safety.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, and `SAFE-THEOREM3` remain pending.
