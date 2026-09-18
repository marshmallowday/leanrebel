# M04 checkpoint — full-game CFR

## Preserved base and review

Work branch: `rebel/m04`. The preserved main commit is
`cf733bd1ffa977681d1197bf80b1dfd7be82ff6e` (accepted M03 documentation).
Its ReBeL run `35285842456` and inventory run `35285842423` succeeded.
Main has not been rewritten or replaced by an unvalidated M04 implementation.
M03's qualified obligations stay qualified. M04 does not assert that later
ReBeL variants, networks, learning contracts or runtime code are verified.

All 23 original files recursively under docs/rebel have now been reviewed,
including every row of paper.tsv, official.json.gz and the expanded child
ledger. The complete source was acquired through the GitHub plugin from
artifact `10523499140` of that baseline ReBeL run. Its ZIP SHA-256 is
`1e99f7d314ccb63bbdf02dcb9ac9cf959c3fbc1952222eaab72913322af04349`.
The starting ledger contains 3052 items: 405 context_indexed, 2596 pending,
11 qualified and 40 verified. No M04 item has been promoted at this checkpoint.

## Current finite-plan slice

`GameTheory/ReBeL/FiniteSites.lean` constructs an all-legal-history cover,
finite information-local pure plans, exact behavioral-to-plan payoff
realization against fixed opponents, and actual attainment of a best response
in the canonical behavioral game. This is not just a characterization of a
maximizer, and the pure plan cannot inspect an opponent's hidden state.

`Examples/FiniteSites.lean` exercises the full M02 two-stage hidden-type game:
arbitrary behavioral opponents have an attaining pure best response; a real
zero-reach branch stays covered; an omniscient finite-plan guess is rejected.
Both modules are explicit public imports and are discovered by compiler,
normal/slow lint and transitive-axiom auditing. Acceptance requires the actual
new source SHA's successful Actions result; file editing alone is not evidence.

Compiler recovery history:
- `7be6d06`: the new module needed its explicit public-root import.
- `f6c9586`, run `35290359135`: a preexisting historical-evidence regression
  incorrectly required future modules to appear in the immutable M03 log.
- `c6b2008`: corrected that regression without relaxing the original 33-module
  build/lint equality. All historical modules must remain in today's actual
  `proof_modules()` consumer, and every new ReBeL module must be in that same
  compiler/lint/axiom consumer. All 34 Python regressions passed. Inventory
  run `35290798215` passed. ReBeL run `35290798213` then diagnosed a nonexistent
  redundant Mathlib import, rather than a proof error.
- `8206392`, run `35291442117`, artifact `10527120553`: real compilation
  identified class reducibility, doc-comment/omit placement and local-instance
  style errors. This slice fixes them; no check is disabled.

## Remaining dependency-closed slices

1. Construct an exhaustive chronological schedule from finite full-AOH sites.
   Derive the root identity from actual unilateral replacements, with equal
   depth and off-path cases; never store hgain as an assumed solver result.
2. Couple all local regret matchers to one simultaneous play trace. Realize
   their payoffs as canonical counterfactual action values; derive uniform
   bounds and a finite-iteration whole-policy regret theorem.
3. Construct own-reach weighted behavioral averages, with zero-reach fallback;
   prove outcome-law equivalence to private independent iteration seeds and
   connect regret to the canonical two-player zero-sum approximate Nash claim.
4. Implement an explicit rational reference solver, prove real refinement,
   fix T=0/1 and zero positive-regret behavior, and check genuine two-stage
   executions against independent exhaustive best responses. Reject simple
   coordinate averaging and shared iteration randomization.
5. Inspect target-SHA compiler, full build, normal/slow lint, architecture and
   transitive-axiom results. Add precise semantic/source evidence to coverage
   and STATUS, preserving old evidence, before declaring M04 complete.

Local proofs for terminal-tolerant local CFR, chronological root decomposition
and reach-weighted means are being developed. They are not accepted evidence
and are not silently counted as a completed generic solver.

## Compiler loop and recovery

All GitHub access and writes use the GitHub plugin. Offline inspection and
arithmetic do not contact GitHub or invoke local Git. A temporary read-only,
branch-scoped workflow exports the pinned Lean/compiler dependency closure
without Git metadata or credentials. Compiler export is separate from proof
compilation. Neither toolchain nor dependency pins are changed. The workflow
is development infrastructure, not an acceptance gate or a new trust axiom.

Read the actual branch ref, newest commit and associated Actions first. Resume
saved source rather than repeating M03. Do not force-push, reset, use worktrees,
or mistake this checkpoint for M04 completion. Recheck main ancestry before
integration; remove temporary compiler-export infrastructure at acceptance.
