# M06 counterfactual envelope bridge

Restart source: ce55384a01cd91b6d8070314074f46690462a25f, retained on
rebel/m06-refresh-checkpoint-20260921. Work continues on
rebel/m06-counterfactual-envelope-20260921. Main remains unchanged.
The base full repository CI 35535912944/job 106144785492 passed. Base ReBeL
35535912927/job 106144785441 was still running at the initial observation.
No older finite-child repair is replayed and no history is rewritten.

## Source-directed next proof

Published supplement Appendix G, Theorem 3 proof (printed pages 21-22), uses
CFR-D regret and the SAME recursively computed continuation at each sampled
iteration. It does not require preservation of exploitation against each
fixed weak opponent. The existing equilibrium-replacement counterexample
must remain; bounded random refresh is a separately labelled variant.

Construct a weaker, opponent-payoff envelope at the positive opponent-reference
information fibers: resolved opponent payoff is bounded by the incumbent MODEL
continuation payoff plus a local allowance. Reweight to the actual unknown-
opponent prefix, compare to its prefix-only deviation, and use the actual
outer trunk regret plus the focal player's full regret. The desired theorem
has no probability-of-refresh penalty and does not assume a fixed-opponent
old-versus-new payoff comparison. Its local envelope remains an explicit
obligation for a source-consistent recursive solver, NOT automatically supplied
by two independently chosen Nash policies.

## Scope and coverage

This is a dependency-closed bridge for SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3, not a claim of completed recursive source correspondence.
No original parent obligation is promoted. The printed all-delta statement
remains distinct from its additive finite-iteration correction. The proof
must retain off-model opponent reach, stopped leaves, the private seed,
actual carried model beliefs and an unknown opponent outside all seed draws.
Every new module must enter target, normal/slow-lint and axiom consumers.
No theorem may assume its own final security conclusion as data.
