# M04 recovery with Actions execution prohibited

## Remote checkpoint inspected on 2026-09-18

- main: cf733bd1ffa977681d1197bf80b1dfd7be82ff6e (accepted M03).
- rebel/m04: 8602bb10305da4163370b2258b9a579d05e9f715.
- This source is already committed on GitHub. Do not restart the finite-plan,
  scheduling or terminal-tolerant local-regret work from an older chat.
- Existing ReBeL run 35297361329, job 105452555180 failed before Lean ran:
  TRANSPORT_REBEL_SOURCE expected 58, got 61. Its other reported zero gates
  include REBEL_NONDEFINITIONAL_TRANSPORT=0. Inspect the three additional
  definitional proof steps rather than removing a gate or assuming a proof error.
- Existing inventory run 35297361348 succeeded.
- Previously pending full CI run 35295577873 for
  9859ae06e9ea99808690167fc47159f857c3de31 has completed successfully.
  This historical success does not validate the newer scheduling source.
- Exact source was obtained through the GitHub plugin from existing artifact
  10528870433. ZIP SHA-256:
  fd043606a444f1ea0535c10ff2ca435501a08fa7261c0bc69eeb46363d6e495e.

## User-authorized acceptance change

The user explicitly prohibited new GitHub Actions executions because of the
usage allowance. Do not dispatch, rerun, or push commits that trigger Actions.
All checkpoint commit messages carry [skip ci]. Existing workflows only use
push, pull_request and manual triggers; no PR is needed for recovery.
Existing run metadata, logs and already-produced artifacts may be read without
starting a runner. GitHub access, writes and ref updates use the GitHub plugin;
no local Git or network access to GitHub is used.

Successful Actions execution is no longer an acceptance requirement for this
M04 task. All other correctness requirements remain: actual Lean checking where
available, source/assumption review, no placeholders or custom axioms, honest
transitive trust evidence, positive/negative examples and rational refinement.
An Actions waiver is not a waiver of a mathematical obligation or a license to
report an uncompiled statement as kernel-checked.

## Remaining work

Read all current docs/rebel files, repair the static architecture regression,
then continue the actual chronological root decomposition, coupled CFR trace,
own-reach behavioral averaging and Nash bridge, and executable rational solver
with refinement and independent best-response tests. Preserve the canonical
Protocol semantics and M03's existing verified/qualified distinctions. Do not
supply a desired regret decomposition as a solver assumption. M04 remains
in progress; this document is a restart checkpoint, not milestone acceptance.
