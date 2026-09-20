# ReBeL status — M06 in progress; M05 accepted

## Active M06 restart point

Continue on `rebel/m06-joint-completion-20260920`; read its actual remote HEAD
and exact-SHA CI before editing. Do not resume from `rebel/m06-recovery` or
`rebel/m06` merely because an older document names them. Main remains the
accepted M00-M05 integration `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

The joint-completion branch contains `b5978ef674f46f02c4b39785b033dd42bdc26ddf`
from `rebel/m06-resume-20260920`. The previous non-fast-forward rejection was
handled without force; both development lines were preserved. At restart,
`cd2f5be3a19ec6774037636070a9478f24cf2676` was five commits ahead of that source.
Its target run `35480034249`, job `105996070767`, failed on nonexistent
`conditionalOracle` and `conditionalOracle_eq` names. The canonical name is
`conditionalOracleValue`, which is a definition. Repair
`943964003e6ae661af85fd3a1a03b5e9493b1527` keeps all statements, premises, and
controls while using that definition. Its target is run `35481397559`, job
`105999754058`; inspect the final result instead of assuming it succeeded.

## Current implementation checkpoint

`CFRDCompletedContract.lean` connects joint completion to the actual solver's
`CFRDLeafOptimal` contract. Factual and unilateral reference query packets are
preserved. Conditional best-response values depend only on decisions along
their legal continuation, so public-state splicing need not equate entire
unrelated policies. Compatible canonical PBS query equilibria and locally
implemented computed responses derive a zero-loss leaf contract. No final
payoff bound is put into a query-data field.

The new module is in the analytic umbrella and declared M06 target list.
Compiler, lint, architecture and transitive axiom validation of its own source
are pending at this checkpoint. This is not M06 acceptance or integration.
See [M06-completed-contract.md](M06-completed-contract.md).

## Remaining M06 boundary

Construct the typed query games, kernel/factual-support identities, public-state
policy splicing, and recursive child solves used by the new theorem. Its
`queries` premise is an explicit outstanding construction, not a claim that
arbitrary PBS kernels or arbitrary independently selected equilibria satisfy it.
Connect finite-iteration child continuation losses and recursive execution to
the existing depth-limited security theorem. Exact query Nash is not a uniform
finite-T conditional guarantee. Keep numerical prediction error, child loss,
optional generic replacement loss, and the finite-T term distinct.

Preserve seed/average, zero-own versus zero-joint reach, and arbitrary-equilibrium
replacement negative controls. Keep the printed and corrected Theorem 3
statements separate. No source obligation is promoted by unverified code.
Coverage remains pending for the full M06 parent obligations; the previous
M00-M05 evidence and every original source identity remain intact.

## Accepted work and historical evidence

The preceding STATUS is preserved byte-for-byte in
[M06-status-before-query-contract.md](M06-status-before-query-contract.md).
It contains the full accepted M05 evidence, qualifications, coverage counts,
and earlier M06 checkpoints. Read it with [M05.md](M05.md) and
[M05-validation.md](M05-validation.md), not as the current restart branch.

M05's accepted proof source is `b1b557b7e3c9471e5f774c7fc400c1665742a614`.
The finite canonical PBS equilibrium/value and adopted Theorem 1 results retain
all documented restrictions. Refuted radial-extension and arbitrary-linear-
combination claims remain refuted, not silently replaced by corrected claims.
M04's accepted source `ee8fdf1d63af8c592d1d2ee4949df385a6341a4f` remains intact.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted on the strict
proof surface. No placeholder, custom axiom, relaxed gate, dependency change,
or unverified merge into main is authorized by this checkpoint.

The complete ReBeL formalization still requires M06-M11. Compiler success alone
does not discharge semantic source matching or recursive solver obligations.
