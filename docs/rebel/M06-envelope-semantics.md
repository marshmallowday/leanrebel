# Counterfactual resolver envelope: semantic review and construction boundary

## What was proved

The comparator is the incumbent model's continuation law, not its payoff
against a particular weak opponent. At each sampled outer iteration and each
positive opponent-reference information/live fiber, CFRDResolverEnvelope
bounds the resolved opponent payoff minus that model continuation payoff.
Stopping has zero gap. Perfect recall supplies the actual unknown opponent's
change of measure, including prefixes with zero factual/model probability.
Only supported conditionals are used; no impossible model PBS is invented.

The reweighted comparison is with a PREFIX-ONLY opponent deviation: it uses
the unknown opponent before the cut and the model policy after it. Hence the
existing searched-site regret bound applies. The focal player's full regret
and the reference equilibrium's minimax guarantee close the zero-sum lower
bound. The final theorem derives both regret terms from the actual noisy
CFR-D recurrence, rather than taking their numerical values as certificates.
The numerical error, focal child loss, finite outer-iteration term and local
resolver-envelope loss remain explicit and separate.

This is a sufficient condition for the derived guarantee, not a necessary
condition for every possible proof of the original algorithm. In particular,
a coherent aggregate recursive argument may avoid a pointwise type ceiling.
The new condition is not relabeled as an assumption of the source paper.

## Scope of actual instantiations

The live HiddenTypes control uses the finite-child noisy outer recurrence,
with numerical perturbation 1/8 and finite-child loss 1/4. Retaining its
constructed continuation discharges the envelope, for any unknown opponent.
The final security theorem is instantiated on that same generated trace.
The reference equilibrium only names the original game value. No child
Nash or leaf-quality bound is supplied to this instance.

This instance RETAINS the already constructed complete child policy. It does
not implement fresh independent recursive re-solving. The example with a
changed policy and lost exploitation is separately a canonical finite matrix
game, not a claim that the retained finite-child control changes its policy.
Zero remaining fuel works with an arbitrary resolver and actual history.

## Counterexamples and non-implications

The existing equilibrium-replacement game now also proves that the universal
opponent model ceiling can hold while payoff against a fixed weak opponent
falls by one. A bad legal candidate violates that ceiling. Thus the ceiling
is substantive, but does not impose preservation of exploitation.

A separate canonical finite mixed type-plan game has a common half/half PBS
and two exact Nash choices of the minimizing opponent. The positive type-zero
value is one against one choice and zero against the other. The game value
and prior coincide, but the coordinatewise ceiling fails. The theorem's Nash
predicates include all mixed deviations, not just two displayed pure choices.
This rules out deriving the local condition from arbitrary independent child
Nash selection. It is NOT a refutation of source-consistent ReBeL recursion.
The supplemental rational enumeration is only an independent sanity check;
Lean proves the actual predicates and inequalities.

## Next source-consistent construction

The published supplement's Appendix G (printed pages 21-22) relates test-time
sampling to the policies in the recursively evaluated CFR-D iterations. It
does not provide an independent theorem preserving exploitation against each
fixed opponent. Appendix I describes the tabular child solves supplying the
continuations. The following is our implementation plan, not an extra source
claim or an already completed theorem.

Build the child policy/value outputs from one coherent solver trace indexed
by the actual current-policy PBS. Preserve the same conditional kernels and
any necessary zero-own-reach completions when the test-time child is invoked.
Use the existing delayed private-child sampling law and cfrDChildResolve_eq
when that child family is the one represented in the parent's continuation.
Then either derive the new local opponent envelope or prove the appropriate
aggregate recursive guarantee, maintaining the actual unknown-opponent law
outside the private seed draws. A solver returned by an independent Nash
existence or minimax selection is not a substitute for this association.

The adaptive complete-plan real-arithmetic child reference remains distinct
from information-set CFR, fixed child iteration counts, and executable
numerical refinement. No original M06 parent is accepted by this dependency
slice. Preserve the printed/corrected Theorem 3 distinction and every prior
negative control. The already validated bounded-refresh variant remains a
separate result with its own conservative switching penalty.

Primary source: https://papers.nips.cc/paper_files/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Supplemental.pdf
