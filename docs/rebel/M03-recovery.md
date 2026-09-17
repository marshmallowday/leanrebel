# M03 recovery and acceptance evidence

## Recovery from the interrupted attempt

The remote refs were read through the GitHub connector. `main` remained at
`db95ea6ad79a26ff753093294722c779e109118d`; `rebel/m03` had retained the latest
checkpoint `51b2330aef0480cf03c86f18b71c3d63143b2977`. No reset, force-push,
worktree, direct local GitHub access, or replay of the completed slices is used.

ReBeL run `35267885960` failed. Its exact-source artifact `10517301374` and
validation artifact `10517765649` were downloaded through the connector.
The source tar SHA-256 is
`88667da06a9207ad60850a4aba5ebac6d2024e117b27bf360db5868e0b3efe61`.
The log shows all other targets built, but PublicSubgame and BeliefStatistic
failed: two set-membership presentations, an unused Fintype section variable,
and a nonexistent Finset.sum_div lemma. The recovery uses explicit target
presentation and the existing division/multiplication and sum_mul lemmas;
no theorem statement, assumption, lint setting, or trust gate is weakened.

This recovery is not an M03 acceptance declaration. Compilation and trust
checks execute only in GitHub Actions. The remaining acceptance review must
cover all ROADMAP M03 conditions, adversarial PBS examples, architecture gates,
coverage/source identity preservation, and the actual final target-SHA logs.
