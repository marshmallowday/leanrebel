# M06 public resolver transfer checkpoint

Resume on `rebel/m06-recovery`. The observed restart ref was
`4034c64f6e177a211c22faf5882e92713161ce33`, not the old 7eec0533 checkpoint.
The intervening implementation is preserved. Main is unchanged.

## Inherited lint repair

The two CFRDPBSQuery fields and the three named local instances in each of
CFRDExecution and CFRDLiveControl lacked documentation strings. The repairs
are saved through `99e07a54d70a5591136dad7be87a0335c684152d`; their declarations,
proofs and all acceptance gates are unchanged. Compiler success must not be
confused with whole-repository normal/slow-lint success.

## Conditional transfer, not a universal replacement rule

CFRDResolve gives the public re-solving interface only the retained private
iteration, public observations and optional model PBS. It has no actual hidden
history or unknown-opponent argument. It may privately sample a new complete
legal profile; the referee uses only its focal policy. Stopped leaves bypass
it entirely.

The local comparison uses live information fibers of the POSITIVE
OPPONENT-reference law, not just the model's on-path posterior. Perfect recall
supplies the density of every unknown-opponent prefix. The proof transfers
a supplied LOCAL continuation comparison to actual carried-state execution.
CFRDResolveSafety connects that loss to the actual CFR-D finite-time bound.
Both core modules compile at `04cf850a16e7cf9a56c3b97f66655f285e88a1d0`;
all five one-stage/belief/control modules compile at
`667b6acbff132ef49d84b05574c94e5554312020`. See M06-resolver-belief.md for target runs.

## Required correction to the generalization strategy

Do NOT attempt to derive zero fixed-opponent replacement loss merely from
old and new policies both being Nash. The proposed implication is false.
CFRDEquilibriumReplacement encodes the canonical finite zero-sum GameForm
with focal payoff matrix

```
           column 0   column 1   column 2
row 0          0          0          0
row 1          0          1          0
row 2         -1         -1         -1
```

Both (row 0, column 0) and (row 1, column 0) are exact Nash equilibria with
value zero. Against fixed column 1, replacing row 1 by row 0 loses one unit.
Both still guarantee zero against every opposing action. Thus security value
and exploitation of a fixed weak opponent are different obligations.
The module is a compiler target in this checkpoint; inspect its exact-SHA CI.
It refutes an invalid proof step, NOT ReBeL's recursive solver or Theorem 3.

The generic CFRDResolverLocal and finite-chain CarriedResolveStepBounds
lemmas remain useful explicit sufficient conditions, not necessary conditions
or consequences of arbitrary equilibrium selection. A general M06 proof must
construct and couple the actual child solver, its value vectors and private
execution, or establish an appropriate counterfactual best-response envelope.
It must not smuggle the stronger fixed-opponent comparison into the oracle.
The live-game positive control supplies its comparison by actual continuation
law equality; it does not discharge this general child-solver obligation.

## Status

This is not M06 acceptance. Preserve numerical oracle error, continuation
optimality loss, replacement loss and finite-iteration error as distinct terms.
Preserve the original printed Theorem 3 and corrected finite-time statements.
Full exact-source compiler/lint/architecture/runtime/axiom checks and a genuine
general child-solver bridge remain required before source-ledger acceptance.
