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

## New proof target

CFRDResolve gives the public re-solving interface only the retained private
iteration, public observations and optional model PBS. It cannot observe the
actual hidden history or the unknown opponent's policy. It may privately
sample a new complete legal profile; the referee uses only its focal policy.
Stopped leaves bypass it entirely.

The loss comparison is local to live information fibers of the POSITIVE
OPPONENT-reference law, not just the model's on-path posterior. Perfect recall
supplies the density of every unknown-opponent prefix. The proof then transfers
the local continuation comparison to actual carried-state execution. The
local comparison is a named, explicit obligation, not a final security fact
returned by the oracle. No claim that ordinary on-path Nash alone supplies it
is made.

This commit is a compiler checkpoint, not M06 acceptance. Inspect its exact
SHA's targeted and full workflows before relying on the new proof. Next:
validate this transfer; derive its contracts for concrete continuation solvers,
compose recursive execution, and connect the accumulated loss to the existing
finite-time security bound and source ledger. Preserve the printed Theorem 3
and corrected finite-time bounds as distinct statements.
