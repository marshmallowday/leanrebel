# ReBeL status — M06 in progress; M05 accepted

## Active M06 restart point

Resume on `rebel/m06-contract-checkpoint-20260920`, which contains the complete
proof source `482ebe19486c92035f395fee92acf2bd49ab183c` and evidence updates.
Read its actual remote HEAD before editing. The source branch
`rebel/m06-joint-completion-20260920` was deliberately left at that source so
its running full validations are not cancelled by documentation commits.
Do not resume from the older `rebel/m06`, recovery, or resume branch.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.

The M06 target build passed on EXACT source `482ebe19486c92035f395fee92acf2bd49ab183c`:
run `35482474735`, successful retry job `106002870720`, 35 declared targets,
3,278 Lake jobs. The initial job `106002635153` failed while downloading Elan
with an SSL connection reset, before compilation; the plugin reran that job
without changing source, dependencies, or verification settings.
See [M06-query-contract-validation.md](M06-query-contract-validation.md) and
[M06-query-contract-compiler.txt](M06-query-contract-compiler.txt).

Full repository CI on the same exact source has now PASSED: run `35482474749`,
job `106002665821`. All applicable build, reuse-signature, Phase 1/2/3
architecture/reachability, full public-library lint, and tracked-cleanliness
steps succeeded. This updates the earlier in-progress observation recorded in
M06-query-contract-validation.md; it does not change any source or audit gate.

Exact-source ReBeL compiler/lint/axiom run `35482474752`, job `106002668307`,
is still running at this update. Re-read it and inspect the transitive axiom
output before promoting any obligation. Its width, static architecture,
ledger/inventory/fixture, and rational Lean runtime/independent-response steps
already succeeded. These intermediate steps are not a completed ReBeL workflow
or a completed transitive axiom audit. The documentation head has its own
checks; do not confuse those with the recorded proof source's runs.
No M06 acceptance or integration is claimed.

## New saved proof and controls

`CFRDCompletedContract.lean` supplies six compiled theorems. They preserve the
complete factual/counterfactual query packet and every conditional deviation
value under joint zero-own-reach completion. Legal agreement only on a kernel's
continuation suffices to implement its computed response. Compatible canonical
PBS query equilibria and those local responses derive the actual all-deviation
`CFRDLeafOptimal` contract at zero loss, rather than assuming that inequality.

Five new compiled HiddenTypes controls cover a live query packet, a factual-zero
history that the counterfactual reference really samples, the absence of its
information fiber from factual play, all behavioral deviations' conditional
value preservation, and an opponent-excluded history that cannot be revived by
uniformizing the focal player. Existing seed/average, live-cut, replacement,
and zero-own-versus-zero-joint-reach controls are unchanged.

An independent rational fixture also checked each player's 1,024 pure opposing
policies. Its pointwise -2 to 0 continuation change is NOT a strict improvement
of the whole information-conditioned mean: that mean is -1 on both sides.
This numerical fixture is supplementary, not a Lean theorem or axiom audit.

## Remaining M06 construction

The final theorem's `queries` premise remains to be CONSTRUCTED for the actual
recursive solver: typed canonical PBS games, matching conditional kernels and
factual type support, canonical Nash premises, and one legal public-state splice
implementing their computed responses. The five new controls validate the
reference-law bridge; they do not supply this general query construction.

A useful next dependency-closed task is to construct the public-state splice
using full AOH `prefixAt`, `prefixAt_infoOf_reaches`, and reconstructed public
history, then discharge the new reachable-agreement premise. Follow with the
actual query-game construction and recursively computed child tables. Do not
replace these tasks by an assumed continuation-value or safety inequality.

Finite-T child continuation quality and carried recursive execution must still
connect to the existing depth-limited security theorem. Exact query Nash is not
a uniform finite-T conditional guarantee. Preserve numerical prediction error,
child loss, optional replacement loss, and the finite-T term separately; keep
the printed and corrected Theorem 3 statements distinct.

The original `SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, and
`SAFE-THEOREM3` parent obligations stay pending. No coverage row, source identity,
accepted M00-M05 evidence, test, or verification gate was removed or weakened.
The complete ReBeL project still requires M06-M11.

## Accepted history

[M06-status-before-query-contract.md](M06-status-before-query-contract.md)
preserves the preceding STATUS byte-for-byte, including accepted M05 evidence
and source qualifications. Read it with [M05.md](M05.md) and
[M05-validation.md](M05-validation.md), not as the current restart instruction.
The old archived STATUS's blob is `8a9fd396bf24b6dc9ecd88aa97aaa8de85d1280d`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed on the strict
proof surface. Compiler success alone is not milestone or source-claim acceptance.
