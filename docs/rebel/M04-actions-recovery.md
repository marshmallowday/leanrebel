# M04 recovery: Actions reauthorized (2026-09-18)

## Authoritative restart state

Read through the GitHub plugin at the start of this recovery:

- main: cf733bd1ffa977681d1197bf80b1dfd7be82ff6e (accepted M03).
- rebel/m04: d15e1de77fd089d97ccdaf767dc5dcf334973ecf.
- Repository visibility is public; the connection reports pull/push/maintain/admin.
- The seven GitHub object/file/ref write operations must not be declared missing
  from a discovery summary. In this recovery create_file and update_file have
  actual callable schemas; writes are made through the GitHub plugin.
- d15e1de already removes the three redundant schedule transports without
  changing the architecture audit's expectations. Do not redo that repair.
- The Actions run collection for that exact SHA was empty (the commit used
  [skip ci]); its proof changes therefore still need target-source validation.

## Current user instructions supersede the earlier Actions prohibition

The user has now explicitly authorized GitHub Actions again. The no-Actions
policy in M04-no-actions-recovery.md and M04-architecture-repair.md is a
historical instruction, not the current one. This checkpoint deliberately
triggers the existing read-only, pinned workflows on rebel/m04. No workflow
permission, toolchain pin, axiom allowlist, theorem premise, or audit gate is
relaxed. New execution results must be inspected before acceptance.

The original task remains: read every file under docs/rebel, then complete M04.
Preserve the existing finite-plan/best-response, exhaustive-schedule and total
local-regret slices. Continue actual chronological root decomposition, a coupled
CFR trace and uniform finite-iteration bounds, own-reach behavioral averaging
and independent-seed/Nash bridges, rational execution/refinement and independent
best-response tests. Do not substitute an assumed decomposition for its proof.

All GitHub reads/writes and commits/ref changes use the plugin. No local Git,
force push, worktree, upstream write, or unverified main integration is used.
The local execution service returned TransportTimeoutError even for basic
filesystem inspection; that is not evidence of a GitHub failure. Actions is
the available compiler loop. Preserve focused remote checkpoints throughout.

This is a recovery checkpoint, not M04 acceptance or a claim that the complete
document reread or new compiler validation has already finished. STATUS and
coverage must continue to distinguish partial work from completed obligations.
