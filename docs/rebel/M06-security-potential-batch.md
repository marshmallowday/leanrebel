# Opposing-player Nash and native security potentials

Parent and accepted dependency:
`799b190595ca6c17893290a8b77ff5fdd056ee22`.
This integrated batch is pending new-SHA Actions. M06 remains incomplete.

## Scope and mathematical derivation

M06 needs safety against an unknown opponent. The previous replacement
bound compared that opponent to the freshly computed average opponent.
Such agreement is not needed for the fresh strategy's one-sided security:
use the OTHER player's Nash deviation, then two-player zero-sum.

Write V_model(fresh) for computed fresh self-play, X_actual(fresh,unknown)
for playing only fresh's focal coordinate against a fixed arbitrary opponent,
and eps for the actual recursive solver's positive tolerance. Then:

```
V_model(fresh) - eps <= X_model(fresh,unknown)
V_model(fresh) - eps - bound * L1(actual,model)
    <= X_actual(fresh,unknown)
OLD_actual - NEW_actual
    <= eps + OLD_actual - V_model(fresh) + bound * L1(actual,model)
```

Both root laws use the SAME unknown-opponent kernel, so the single root
charge follows Markov contraction. No opponent-to-model kernel charge or
old-to-new policy closeness is used. The signed incumbent surplus
OLD_actual - V_model(fresh) is explicit and may be large or negative.
This is an alternative bound, not a claim of uniformly smaller numerical
charges than the earlier two-root/two-opponent bound.

PBSRecursivePotential supplies the generic opposing-player argument, one
root transport, actual recursive-Nash instantiation and a direct finite
private-draw model-security result. The latter is exact on the model root
law; it does not claim that actual conditional roots equal a stored PBS.
The opponent is chosen outside the private draw.

For each supported conditional fiber of the accepted canonical key,
PBSRecursiveGroup_loss_eq identifies the exact common old/full-profile and
fresh computation. The new charge is eps plus the potential above, computed
on the fiber's history marginal, and averaged with ACTUAL label weights.
Uncertified cells keep exact signed cost. Canonical grouping preserves
saved joint PBS and incumbent correlation and needs no caller certificate.

PBSRecursivePotentialSecurity retains the actual 2*bound*unsupportedMass
penalty needed to compare native private draws to their averages.
Its recursive budget advances the complete native carriedMemoryStep law.
The signed telescope and actual finite noisy sampled parent then give:

```
reference_value
  - (Cerror*prediction_error + Cfinite/sqrt(T) + 2*child_loss
     + native_potential_budget)
  <= actual_private_recursive_payoff_against_unknown
```

The parent supplies initial security and the recursive solver supplies Nash;
neither is assumed as an input certificate. The original-game reference
equilibrium only anchors the value. Noise contracts, positive tolerances,
finite histories/legal actions, full-AOH perfect-recall construction,
zero-sum payoff bounds and horizon alignment remain where needed.
In particular each config cuts.sum equals its stage fuel plus ALL future
stage and late fuel. Solver behavior, fallback and native updating are unchanged.

## Integrated consumers and independent controls

The hidden-type examples retain the actual parent bias 1/8, child loss1/4
and bound2. Parentcut1/fresh[1,1]/stage1/late1 and
parentcut2/fresh[1]/stage1/late0 both compare horizon3. Additional consumers
cover uncertified exact cost, empty stages with positive late2, and the
actual three-level [1,1,1] private solver at its initial PBS against an
arbitrary opponent, with tolerance1/8.

Five Fraction tests independently check:

- 81 finite matrix/profile/opponent combinations, both players' security
  and private pure-policy mixture equality.
- 72 root/profile comparisons, distinct root and surplus terms, and a
  constant-action payoff example making the single L1 root coefficient sharp.
- Matching pennies: exact Nash secures zero against a pure opponent while
  replacing an exploiting incumbent loses1; negative incumbent surplus is
  retained. Tolerance zero alone cannot bound replacement loss.
- Nine conditional-cell laws with actual frequencies; erasing private
  incumbent/history correlation changes value; actual unsupported mass and
  signed uncertified costs remain visible.
- 27 full-state forward schedules, retained versus resampled late draws,
  empty schedules and independent finite-T/prediction/child terms.

These are independent rational controls, not executions of CFR or Lean.
They will run in Actions; no local test result is claimed.

## Precommit type and semantic review

Read the actual signatures of isNash_iff, euPreferenceWithin_apply,
behavioralBeliefForm, PublicBelief.continuationLaw,
IsZeroSum.expectedUtility_one and twoPlayer_cross_profile. Both player cases
use the opposing deviation and the correct cross-profile equality direction.
The model-security helper precedes section Fintype variables because it
requires no enumeration. Root variation introduces only Fintype History;
action finiteness starts at actual recursive solver instantiation.

Read actual runBehavioralFrom_atomVariation_le, executionKernelCharge_self,
abs_expect_sub_le_atomVariation, pbsRecursiveDepth_isNash,
pbsRecursiveDepthDraw_value, recursivePolicyValueChange and group_loss_eq.
The recursive Nash and root/model helpers use explicit @ arguments for
protocol, all six fullInformation universes, instances and observation index.
Draw equality supplies explicit noise/cuts/M/fallback/payoff/bound/belief,
tolerance/unknown/who/fuel/value rather than reverse-inferring the model.
The signed direction is OLD minus NEW; the absolute root lower bound has
the same orientation. No new PublicBelief.condition or casts are introduced.

Followed those exact types through all conditional charge, native budget,
signed telescope, finite-parent security and five concrete consumers.
Memory K and label carriers retain independent universes. State.history's
full signal index stays attached to its saved PBS. Fiber agreement is the
accepted automatic canonical-key theorem. Actual next laws and tail fuel
are unchanged; Fin t sampled plays are shared by prefix, entry and runner.
The two horizon3 examples, full Choice/InfoState instances and positive
late tail match the accepted parent consumer signatures.

Public declarations and local instances have documentation. All new Lean
lines are at most100 UTF-16 code units. Existing transport-source regex
after comment removal has no matches; no change/cast/HEq/recursor plumbing,
warning suppression, placeholders, custom axioms or heartbeat increase.
All18 public names were checked against the complete accepted targeted/global
axiom names without collision. None of these static checks is compilation
or execution of the repository audits. New-SHA Actions remains required.

## Validation surface and batch boundary

The batch adds2 core modules,1 example and5 Python tests. Registration only
adds targets:190->193 build targets,152->155 targeted modules,
292->295 global modules,230->235 Python tests. Existing workflows and audit
criteria are unchanged. The exact799b190 acceptance is recorded separately
in M06-query-cost-799b190-accepted.md and is not reused for this source.

Dependency-ordered remaining work:

1. Validate this full batch at its own SHA; repair all observed causes together.
2. Relate successive actual conditional self-play potentials and incumbent
   values while controlling actual conditional-root and support terms.
   The opposing-player argument removes any need to posit unknown-opponent
   agreement for fresh security; it does NOT make the surplus small.
3. Identify the relevant internal chance-rooted child and fresh original-game
   solve, including posterior, protocol-dependent noise, fallback, budget,
   clock and root encoding. Equal PBS law alone is insufficient.
4. Combine the small-rate argument with actual native recursion and review
   SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 against pinned sources.

Items2/3 have a substantive mathematical dependency boundary: a potential
difference is not a proof of cross-query value stability or computation
identity. This batch integrates every dependent layer through actual-parent
security and examples rather than splitting by files or short lemmas.
No general vanishing rate, training convergence, last-iterate guarantee,
selected-profile/target-Nash-value identity, or M06 completion is asserted.
Original/corrected Theorem3 formulas remain distinguished in
M06-theorem3-interpretation.md. Finite T and child loss are independent.

Frozen coverage.json and accepted source journal pins remain unchanged.
The old owner ledger is preserved at
M06-kernel-value-transport-coverage-at-799b190.json with its original blob
14f1f5ac13fe9f2fd5b9f86ea852c2e2cc199461.
