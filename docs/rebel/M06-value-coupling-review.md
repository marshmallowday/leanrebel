# M06 directed payoff coupling: semantic review

## Scope and dependency

This is a conditional source-level bridge, not acceptance of M06 or a proof
that native CFR-D yields a vanishing stability rate. It continues the
one-sided-value question recorded in the c984277c fiber-lint checkpoint.
It supplements, and does not replace, the L1 outcome/fiber source bound.

The strict proof uses the existing FinDist, canonical protocol histories,
information-local behavioral profiles, unilateralReferenceLaw and the actual
privateCarriedPrefix. There is no new game/probability semantics, independent
seed/history resampling, changed posterior, or root-security field assumed as
an input. Existing parent and child solver constructions are left unchanged.

## Exact new quantity

For a finite joint law J of an old outcome x and a new outcome y, define

    C(J, u, v) = E_J[max(0, v(y) - u(x))].

`expect_sub_le_directedValueCost` requires both exact pushforward equations:
J.map fst = old and J.map snd = fresh. It proves

    E_fresh[v] - E_old[u] <= C(J, u, v).

The proof rewrites expectations using those marginal identities and applies
pointwise monotonicity. A payoff decrease is harmless in this direction.
A supported pairwise bound on v(y)-u(x) implies a bound on C, and a supported
non-increase proves C=0. These generic statements need neither a finite carrier
instance nor bounded payoffs, because each FinDist already has finite support.
The caller supplies J; the code does not assume it is optimal or independent.

## Connection to actual source safety

`cfrDFreshValueChange_le_couplingRate` uses one joint continuation law for each
initial history. Its marginals are exactly the old and new runBehavioralFrom
laws, and its payoff is the opponent's actual terminal payoff. A nonnegative
uniform bound on C gives the same bound on the positive OLD-query value change.
The bound is stated for all histories, including histories absent from the
actual unknown-opponent path; no fallback posterior is identified as factual.

The supported query theorem retains the reference-fiber transport charge,
including NEW-only atoms and vanishing NEW query support. Multiplication by
2*B and the existing factor-2 conditional transport bound yields 4*B*rho.
The resulting actual prefix bound is

    childLoss + valueRate + 4*B*referenceRate.

Perfect recall and the existing unilateral-density theorem supply support
under the OLD unilateral reference for every actually reached opposing
prefix. The integration still uses the original private seed/history joint
law. No division by an unproved positive reach probability is added.

The generic result bounds the computed weighted charge. The final actual-game
security consumer also uses the inherited solver-quality/payoff-bound
hypotheses through `freshChainControl_biased_weighted_security`; omitting a
payoff bound from the numerical charge-comparison lemma does not remove it
from security. The concrete B is 2, so the value budget calls the previous
outcome-rate budget with valueRate/2 and charges valueRate exactly once.
Same-cut source-law preservation discharges referenceRate=0 for the real two
fresh solves. The parent bias 1/8, finite-T term, old-child tolerance 1/4 and
new-child tolerance 1/8 are retained. Small C is not derived from Nash.

## Positive and adversarial controls

The positive control uses two payoff types with probabilities 1/2 each and
payoffs -1 and +1. Every old outcome has label false and every fresh outcome
has label true. The explicit coupling preserves each type and flips only its
payoff-irrelevant label. Thus the supports are disjoint and L1 variation is 2,
while directed payoff cost is 0. The expectation comparison actually calls
the generic coupling theorem; the example is not merely a constant-payoff
simplification. Both marginal mass formulas are proved.

The direction control gives cost 0 for payoff 1 -> 0 and cost 1 for 0 -> 1.
The incorrect-marginal control rejects a fabricated zero-cost joint law whose
new marginal differs from the claimed fresh outcome law. A pure-law control
is used here only to isolate the missing marginal, not as the positive
nontrivial two-type example.

An independent Python Fraction calculation also gave L1=2, C=0 and both
expected payoffs 0. This is a diagnostic cross-check, not kernel evidence.

## Preservation and static checks

The three new module blobs were matched locally using Git's blob hash format
without invoking any local Git command. Target and umbrella edits are exact
append-only additions. The supplemental audit retains all prior 93 modules
and appends three, giving 96. The M06 target list retains 131 and appends three,
giving 134. No inherited workflow, gate, allowance, pin or negative test is
removed. The historical coverage.json is byte-for-byte unchanged; the scoped
companion record identifies the four still-pending parent obligations.

Offline structure checks passed for 3054 expanded ledger entries and the
pinned inventory. All 76 Python tests passed under `-W error`. Every new Lean
line passes the existing 100 UTF-16-code-unit limit. No placeholder, custom
axiom or warning-suppression option was added. These are static checks, not
substitutes for the exact-SHA compiler/lint/transitive axiom results.

## Explicit remaining obligations

Construct quantitatively small directed couplings or a different justified
one-sided value bound for the native/late-training solver queries. The present
uniform per-history premise can be stronger than a weighted query premise;
it must not be silently weakened or called discharged. Later independent
carried-PBS re-solving, native first-exit bounds and CarriedResolveStepBounds
remain separate obligations. The native-iteration sampler is not identified
with coherent final-average sampling. The printed and corrected Theorem 3
claims, especially finite T at zero oracle error, remain distinct.

## Limitation of the certificate (not a native-solver counterexample)

Equal mean payoffs alone do not force this directed coupling cost to vanish.
Take a deterministic old payoff 0 and a new payoff -1 or +1 with probability
1/2 each. Both means are 0, but every marginal-preserving coupling has cost
1/2, because the old payoff is constant. The arithmetic was also checked with
Python Fraction. This is an elementary diagnostic, not a new kernel theorem
or a counterexample to the paper's native solver.

Consequently, scalar approximate Nash/value accuracy must not be reported as
a construction of a small-cost coupling. This certificate is sufficient and
value-sensitive, not necessary for one-sided expected-value stability. The
next native-rate proof may need a direct signed-expectation estimate instead;
its old-query conditioning and actual seed/history weights must be retained.
