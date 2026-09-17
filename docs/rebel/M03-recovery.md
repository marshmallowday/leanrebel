# M03 recovery and acceptance evidence

## Recovery from the interrupted attempt

Remote refs were read through the GitHub connector. `main` remained at
`db95ea6ad79a26ff753093294722c779e109118d`; `rebel/m03` retained checkpoint
`51b2330aef0480cf03c86f18b71c3d63143b2977`. No reset, force-push, worktree,
direct local GitHub access, or replay of completed slices is used.

ReBeL run `35267885960` failed. Exact-source artifact `10517301374` and
validation artifact `10517765649` were downloaded through the connector.
The source tar SHA-256 is
`88667da06a9207ad60850a4aba5ebac6d2024e117b27bf360db5868e0b3efe61`.
PublicSubgame had two set-membership presentation errors and an unused
Fintype section variable; BeliefStatistic referred to nonexistent Finset.sum_div.
Commit `1e85d2e59fc9fa98f55afce4699cfbe99dfb5771` repaired these.
Run `35269665756` compiled BeliefStatistic and exposed a documentation-comment
placement error before `omit`, repaired in the next checkpoint.

Commit `6c56ae6f45b754b1f5c8fbe1eccecceae87a4ac6` added same-game PBS
correlation/payoff tests, actual Bayesian referee evaluation, all-policy Nash
correspondence, off-path controls, fully public degeneration, card exclusion,
and the Figure 1b zero-leaf diagnostic. Its exact-source tar SHA-256 is
`ec5c30c947d90cffa3a3e42b1f9a718801f5055e35a2a4cd5045ecfa5440c624`.
Run `35270513857` compiled every general M03 module and BeliefSearch. It found
an unapplied-function unfolding issue in PublicBelief's payoff test and an
unnecessary second split in CompactCards. Compiler-generated sorry terms in
failed logs are cascading error recovery, not authored placeholders. Failed
jobs are never accepted as complete proof evidence.

Commit `2d77105d23fb317c30c2584661ae52d826b33b61` integrated every module into
the opt-in root, added the nonuniform public-observation test, wrapped four
overlong lines, and deleted the temporary environment-export workflow.
Run `35271701154` compiled CompactCards but exposed missing explicit reductions
at the canonical history root and in BayesObservation. These were repaired in
`5e3efa33dcda3402f61bc731f11093becada6313` without changing their statements.

## First complete compiler and axiom pass

At `5e3efa33dcda3402f61bc731f11093becada6313`, run `35272434274`, job
`105374816107`, all 31 audit modules built (1770 build jobs), and the actual
log reports `REBEL_AXIOM_AUDIT_PASS declarations=1282`. Only propext,
Classical.choice, and Quot.sound occur. This includes the nonuniform Bayes
posterior, same-game unequal payoff control, and both Nash directions.
Source artifact `10518752218` has source-tar SHA-256
`85bce96d4ae21218e73181da0fe40216502ec87307cf594e81b20af8644fb7a9`.
Validation artifact `10519378032` preserves the actual output.

That job still failed full/slow lint: three missing documentation strings,
a redundant specialized simp rule whose left side the general rule already
reduces, and an unnecessary Fintype-history argument on the unnormalized
weight equality. The recovery adds documentation, retains the specialized
theorem as an explicit rewrite lemma with its original proof and statement,
and removes the unused finite-history assumption (strengthening that equality).
The normalizing operations still require a finite carrier. No nolint entry,
linter option, expected architecture count, dependency pin, proof statement
weakening, or trust allowlist change is used.

M03 acceptance still requires target-SHA full/slow lint, full architecture
and public-library CI, inventory checks, and the evidence/STATUS update. A
compiler/axiom pass alone is not the milestone acceptance declaration.
