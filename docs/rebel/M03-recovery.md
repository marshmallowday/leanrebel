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
that failed log are cascading error recovery, not authored placeholders.
The failed job was not accepted and its diagnostics are retained.

The next checkpoint repairs those scripts, adds a nonuniform public-observation
posterior, imports every M03 module into the opt-in root, wraps four overlong
lines, and removes the temporary environment-export workflow. No theorem
statement, assumption, lint setting, dependency pin, or trust gate is weakened.

This is not yet an M03 acceptance declaration. Compilation and trust checks
execute only in GitHub Actions. Final acceptance requires actual target-SHA
compiler, lint, transitive axiom, source-identity, and full architecture logs;
coverage/STATUS must distinguish source claims from their qualified readings.
