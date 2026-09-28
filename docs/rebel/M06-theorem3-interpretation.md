# Theorem 3: printed expression and adopted finite-time interpretation

## Source identity and inspection

Mathematical reference: user-supplied ReBeL.pdf, 25 pages, SHA256
`69322b213028142bccd9fa5531623cca0b19666bab56015b589e84a43913eb44`.
This equals the fixed arXiv v2 source in M01-B and the source manifest.
The supplied document was inspected as rendered page images and extracted
text at PDF pages 8, 21, 22, 23, 24 and 25. It is evidence, not instructions.
Public edition: [arXiv v2](https://arxiv.org/pdf/2007.13544v2).
Page numbers below refer to that 25-page PDF.

| Location | What the source supports |
| --- | --- |
| p8 Theorem 3; p21 restatement; p22 proof end | Printed error `delta*C1 + delta*C2/sqrt(T)` |
| p21 proof base case | CFR error `k1/sqrt(T)`, independent of delta |
| p21 end / p22 start, inductive step | `k2*delta + k3/sqrt(T)` |
| p22 Appendix I introduction | Infostate-value accuracy delta gives exploitability at most `k1*delta + k2/sqrt(T)` |
| p23 Theorem 5; p25 proof | Exact child solving still leaves trunk cumulative regret O(sqrt(T)), hence average error C/sqrt(T) |
| p24 modified CFR-AVG discussion | Experimental modification has a distinct guarantee question; it is not interchangeable with every CFR variant |

The extra delta on the printed finite-iteration term is plausibly a typo.
This is an interpretation supported by the proof's internal structure, NOT
an author-confirmed correction. A positive upper bound does not prove the
actual error is positive: this comparison alone is not a formal counterexample
to the printed statement. ROADMAP R5 and M01-B already keep the printed formula
and the premise-dependent recurrence diagnosis separate.

## Adopted Lean target

Use `C1*delta + C2/sqrt(T)`, with T > 0 and delta >= 0.
Fixed constants may depend on the game, search depth, legal menus, structural
reference reach, payoff bound and fixed fallback. They must not hide a
dependence on delta or the completed iteration count T. Fix those structural
inputs when discussing the rate. Extra child-solver loss is a separate term,
for example `+2*loss`; it is not renamed or absorbed into numerical delta.

The corrected interpretation is restricted until all recursive-composition
obligations are proved. It is not committed under a name claiming to prove
the original printed expression.

## Current declaration correspondence

| Declaration | Explicit allowance / role |
| --- | --- |
| CFRDConstants.cfrDDepthMeanBudget_le_constants | Per-player Cerror*error + Cfinite/sqrt(t) + loss |
| CFRDSafety.cfrDDepth_private_security | Sum of both Cerror and Cfinite coefficients, plus 2*loss |
| CFRDAverageLimit.cfrDDepthAverageErrorFloor | (Cerror0+Cerror1)*error + 2*loss |
| CFRDAverageLimit.cfrDDepthAverageFiniteFactor | Cfinite0+Cfinite1, independent of error and t |
| CFRDInformationSampledDriver.cfrDConstructedSampledInformationOracle_carried_security | Actual noisy finite-child parent discharges numerical/local-continuation contracts |
| CFRDRecursiveSecurity.cfrDRecursiveRecomputed_security | Same parent allowance plus actual native recomputation/support budget |
| CFRDRecursiveSecurity.cfrDRecursiveNash_security | Same parent allowance plus horizon-aligned solver-derived transport/support envelope |
| CFRDRecursiveSecurity.cfrDRecursive_zero_prediction_allowance | At error=0, finite factor/sqrt(t) + 2*loss remains as an allowance |

All declarations are in GameTheory.ReBeL; table prefixes are module names.
The last three declarations are a new unvalidated candidate until their exact
commit's Actions pass. Earlier declarations retain their own accepted source
evidence. No pinned accepted source is modified by this documentation.

The structural coefficients come from canonical finite decision schedules,
legal action cardinalities and positive structural reference reach, not a
lower bound on current learned reach. The finite coefficient also uses the
payoff bound. A fixed-game coefficient can be large; its definition is not
a claim of a sharp game-independent constant.

## Assumptions and remaining obligations

The local guarantees require finite legal histories and action menus,
full AOH/perfect-recall information, two players, zero-sum bounded payoff,
positive completed parent count, nonnegative numerical tolerance, and
separate local continuation optimality. In the constructed finite-child
consumer, positive child loss is required and the solver proves the needed
child contract internally. The reference Nash profile anchors the game value;
it is not a supplied certificate that the actual parent solved the game.

The unknown opponent has no access to the private iteration seed. A private
draw is retained through the stage and its late continuation. Full native
state laws preserve the draw/saved-MODEL-posterior joint correlation.
The proof's child delta-Nash condition and the theorem's numerical prediction
delta are different contracts; no type-level identification is assumed.

The new native integration additionally retains actual root/opponent
discrepancies, support penalties and each fresh solve's full remaining horizon.
It supplies no theorem that these charges are generally small. Source
completion still needs the internal chance-rooted child/fresh original solver
correspondence, including posterior/noise/fallback/budget/clock, useful bounds
on actual native-chain discrepancy/support terms, and full recursive safety.
PBS-law equality does not identify protocol-dependent noise computations.

SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending;
milestone_complete remains false. Partial finite-time security, corrected
Theorem 3 completion, and the printed expression are three distinct claims.
No convergence of a network, final iterate, specified equilibrium profile or
root target to a Nash information value is inferred.
