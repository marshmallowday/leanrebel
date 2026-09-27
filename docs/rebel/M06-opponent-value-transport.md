# M06 changed-opponent value transport candidate

## Selected source and authorization evidence

The GitHub plugin read the connected login as marshmallowday, repository
permissions admin=true and push=true, and collaborator permission admin.
The available write route is Git Data blobs, tree, commit and non-forced ref
update. No probe commit or test file was made.

Default main is 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Continue rebel/m06-kernel-value-repair-20260927 from its re-read HEAD
9457c198126f3c8b7cb1045bbed2e0053788636f. It contains the depth-native solver,
compatible-kernel transport and subsequent compiler repairs. It is 369 commits
ahead of main with zero commits behind. The current STATUS directs continuation
here. The branch listing marks it unprotected, repository rulesets are empty,
and the all-state PR list is empty. The related 20260927 heads and their commit
messages were inspected, including the divergent f345910 sibling: the selected
branch preserves the repaired observable control and has successful exact-SHA
validation. Selection is based on source/history and validation, not timestamp
alone. No PR, merge, main update, force update or dependency change is included.

## Baseline acceptance inspected through the plugin

All of these are for 9457c198126f3c8b7cb1045bbed2e0053788636f, not this extension:

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| M06 targeted proof feedback | 36293799005 | 108548763050 | success |
| ReBeL checks | 36293799056 | 108548806226 | success |
| CI | 36293799070 | 108548896246 | success |

Complete decoded job logs were read through the GitHub plugin. Target output:
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1899 and
EXACT_LEAF_VALIDATION_PASS modules=116. Global output:
REBEL_AXIOM_AUDIT_PASS declarations=5049 and
REBEL_VALIDATION_PASS modules=259. All 1899 target and 5049 global axiom
records, including multiline records and the named kernel controls, were
parsed; none contain an axiom outside propext, Classical.choice, Quot.sound.
All 116 target lint passes were present. Full CI build, full-library lint,
inventory/type checks and Phase 1/2/3 architecture checks succeeded.
The pinned toolchain reported Lean 4.33.1.
Artifacts were inspected as metadata (not downloaded/re-executed):
target 10923467220, global 10923767898, source 10922777797,
full CI 10923348310. Their workflow head SHAs match the baseline.

## New mathematical dependency

ROADMAP M06 and the existing kernel-value ledger explicitly leave changed
opposing policies open. Extend the same three already audited modules.

For old/fresh compatible root kernels K,L, let d be their full L1 discrepancy.
For a fixed own response r, c(r) is executionKernelCharge between the two
profiles after replacing the own coordinate by r on BOTH sides. It starts at
K and uses first-profile prefix weights at every step. Existing canonical
execution transport gives payoff drift at most B*(d+c(r)).

Construct rOld and rFresh using the already proved simultaneousResponse for
the actual old/fresh Eq. (1) optima. Set cOpt=max(c(rOld),c(rFresh)).
Cross-domination of these two legal responses gives optimum drift at most
B*(d+cOpt). Consequently, signed gap drift is at most

    2*B*d + B*(cOpt+c(retained)).

This is a derived cost of source kernels, not a value-stability conclusion
assumed as a certificate. Both optimizing policies are needed; only charging
the old optimum is invalid. The retained response also needs its own charge.
Type domains, compatible off-path completions and tied maximizers are allowed.
The horizon and payoff are common. When profiles agree the execution costs
vanish. No on-path conditioning or own-type mass division is introduced.

The actual noisy pbsInformationDepthCFR consumer averages this cost under the
same correlated, event-selected seed/type query. Fresh comparison opponents
may depend on the seed. They are separate from the arbitrary execution
opponent used to select the query. The old depth budget keeps its finite-T,
noise and positive child-loss terms and its event probability denominator.
The newly averaged cost is not divided by event probability a second time.

## Controls and semantic limits

A Lean zero-fuel control separates nonzero root-kernel drift (two units) from
zero execution cost even for different opponents. A live Lean consumer compares
a genuinely noisy two-iterate parent with a separately constructed budgeted CFR
child at the changed pure-root belief, retaining the parent iterate as own
response. Existing changed-kernel, off-path, impossible-event and changed-
opponent counterexamples remain. Four new independent Fraction tests cover
4608 exhaustive deterministic transition/root/response cases, stochastic
opponent kernels, the necessity of both maximizing responses, and the
necessity of the retained-response cost. CI must execute them; their source
presence is not a test result.

This closes a candidate changed-opponent value/gap transport dependency only.
It does not make the execution or root costs small, identify supplied fresh
slices as actual recursive posteriors, or construct signed CarriedResolveStepBounds.
Small primitive support leakage, actual posterior identification, late-value
composition, and the original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR,
SAFE-THEOREM3 acceptance remain open. Learner convergence is not test-time safety.

## Validation of this extension

Pending the new exact commit's GitHub Actions. No Lean shell was used locally
or inside the plugin. Existing 154 target names and 116/259 audit module sets
are unchanged: this extension adds declarations to their existing modules.
No workflow, auditor, expected gate, dependency pin or original theorem
statement is weakened.

Re-read workflow triggers: CI push (all branches), ReBeL checks push main or
rebel/**, targeted push rebel/m06* plus the listed Lean/target/auditor paths.
The three changed Lean files satisfy those path filters. Check all three
distinct runs at the new SHA. After verifying their creation, schedule this
chat once for approximately 50 minutes after the branch ref update, explicitly
in Asia/Tokyo. Do not continuously poll to completion.
