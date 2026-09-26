# M06 randomized resolver support controls

This checkpoint extends candidate 9894e45bbc0505debd44957a4a7446302d2b7902
without changing its seven support declarations. Its source target run was
36280503612 / job 108511290081, still compiling when the controls were prepared.
It was not declared passed. A same-branch successor may cancel that candidate's
in-progress workflows; the successor must pass with its own exact SHA.

## Lean consumers in the existing audited example module

`GameTheory.Analysis.ReBeL.Examples.PBSOpponentModelTransport` retains all
original examples and adds:

- `HiddenTypes.pbsOpponentSupport_randomized`: instantiates the bound with the
  actual `pbsCarriedDepthResolver`, two outer parent iterates, cut 1, remaining
  1, payoff-bound input 2, child tolerance 1/8 and execution fuel 1. Prediction
  perturbations remain arbitrary; this is a support transport bound, not an
  assertion of equilibrium accuracy or small leakage for arbitrary noise.
- `HiddenTypes.pbsOpponentSupport_stopped_missing`: the canonical stopped
  transition preserves missing belief with probability one and charge one.
- `OpponentModelTransport.randomized_model_pooling_undercharges`: a private
  1/4 versus 3/4 draw, disjoint selected model supports and a constant actual
  history give paired failure 1/4, while pooling model laws first yields zero.
  The event explicitly reads both coordinates of the retained finite-law pair.
- `OpponentModelTransport.randomized_selected_model_supported`: the same
  nontrivial draw has zero failure when each selected model executes itself.

These are candidate Lean declarations until exact-source compilation, lint and
transitive axiom records are inspected. Finite-law controls are not asserted to
be outputs of a CFR recurrence; the separate HiddenTypes consumer uses that
actual recurrence.

## Independent exact arithmetic

`scripts/rebel/tests/test_resolver_support.py` adds eight Fraction-based tests.
The exact local copy passed `python -W error -m unittest discover -s
/mnt/data/resolver_support -v`: eight tests, including all 4,374 combinations
of incoming point history, prior grid and six binary-kernel grid parameters.
Each comparison retains the private resolver weights 1/4 and 3/4. Additional
controls retain memory/model pairing, detect wrong-prefix weights, permit
arbitrary changes of positive weights inside support, exclude zero-weight
profiles from required support dominance, and document stopped/missing cases.
These checks are arithmetic evidence only, not Lean execution or a refinement
proof. Repository-wide Python, coverage and inventory must be checked on the
successor source through CI; the prior 112-test pass is not reused.

## Unchanged boundary

No original test, statement, fixed dependency or CI gate is removed. The
existing target and axiom lists already contain both edited Lean modules;
new declarations are discovered dynamically. M06 remains incomplete. The
new transition rate still needs finite-schedule composition and a small
source-specific quantitative bound, separately from signed value/security
comparisons. See M06-resolver-support.md and STATUS.md.
