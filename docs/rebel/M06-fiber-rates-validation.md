# M06 fiber-rate implementation and validation checkpoint

## Exact source and continuation

Lean source: `4b4395714c62ac8fca0974f1254b7f86c832cd38` on
`rebel/m06-fiber-rates-20260925`.
Documentation checkpoint branch: `rebel/m06-fiber-checkpoint-20260925`.
The checkpoint adds documentation only; it does not replace or move the source
branch while its exact-SHA workflows execute. Inspect the following runs before
acceptance or additional source changes. All remote operations use the GitHub
plugin, not local Git. Main and all accepted predecessor refs are unchanged.

## Observed validation state at this checkpoint

| Source | Workflow / run | Job | Observed result |
|---|---|---|---|
| 4b439571 | M06 targeted / 36084113146 | 107912150501 | All declared targets compiled successfully; supplemental lint and transitive-axiom step still running |
| 4b439571 | Full CI / 36084113058 | 107912146899 | In progress |
| 4b439571 | Independent ReBeL / 36084113120 | 107912151577 | In progress; ledger/fixtures and rational solver steps passed |
| 4b439571 | Exact source snapshot / 36084113120 | 107912151368 | Success |
| 4b439571 | Source inventory / 36084113156 | See run | Success |
| 45a59f97 | M06 targeted / 36082610875 | 107907611579 | Success, including supplemental lint and transitive-axiom audit |
| 45a59f97 | Full CI / 36082610831 | 107907668869 | Success, including all three architecture audits and library lint |
| 45a59f97 | Independent ReBeL / 36082610843 | 107907671925 | Still in progress when last inspected |
| 45a59f97 | Exact source snapshot / 36082610843 | 107907671645 | Success |

Target workflow links:
- https://github.com/marshmallowday/leanrebel/actions/runs/36084113146
- https://github.com/marshmallowday/leanrebel/actions/runs/36084113058
- https://github.com/marshmallowday/leanrebel/actions/runs/36084113120
- https://github.com/marshmallowday/leanrebel/actions/runs/36084113156

The repaired predecessor's targeted audit printed
`EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1440` and
`EXACT_LEAF_VALIDATION_PASS modules=93` under Lean 4.33.1. These counts describe
45a59f97, NOT the newer fiber-rate source. Inspect the new source's own output.
Allowed axioms remain only `propext`, `Classical.choice` and `Quot.sound`.
The declared M06 target list has 131 entries; neither it nor the 93-module
supplemental audit list was shortened. Both edited modules were already listed.
No workflow, dependency pin, exception allowance or test was weakened.

The predecessor artifact metadata was re-read through the plugin:
`m06-targeted-45a59f97b3e02de43cd367c15e8c7f187654e874`, artifact 10842422210,
SHA-256 `d3bc59f890070028778256316a1987a39b16c1959940c1a5457dc0a55f1690f3`.
The decoded job logs, rather than a source grep, supplied the axiom evidence.
A local attempt to inspect the downloaded ZIP failed with container ClientError;
no local compilation or successful local artifact recheck is claimed.

## Preserved compiler loop

1. Original source bd5cdaa304cb0791379c94fd0454ed28eabb683d failed in
   Examples/CFRDSourceRates.lean. Repair 45a59f97b3e02de43cd367c15e8c7f187654e874
   changes eleven proof bodies, not their statements: explicit pure-probability
   simplification, expectation rewrite order, supported-query branch reduction,
   and the correct side of addition monotonicity.
2. The quantitative candidate f96c6183de2dcc8c0692106c541d433e6cd5bd72 compiled
   the core rate lemmas and finite controls, but the game example failed at
   `freshChainControl_parent_fiber_zero`. Target run36083517720/job107910323337
   records the failed direct rewrite through reduced/full model aliases.
3. e1d7d3f2654e7528387bbc397772a21cbd41439d introduced a typed local
   reference-law equality before rewriting. A duplicated `Prod.fst` argument
   introduced during that whole-file edit was immediately restored by
   4b4395714c62ac8fca0974f1254b7f86c832cd38. The mistake remains visible in
   history; no success is attributed to the intermediate commit.
4. At this checkpoint the corrected source has passed compilation. Remaining
   lint/axiom and independent gates must be checked at its own exact SHA.

## Semantic review of the new proof surface

Owning core file: `GameTheory/Analysis/ReBeL/CFRDSourceRates.lean`.
Owning consumer: `GameTheory/Analysis/ReBeL/Examples/CFRDSourceRates.lean`.

`cfrDFreshValueChange_le_outcomeRate` bounds positive OLD-conditional value
change by B*eta, where eta bounds the L1 variation of ACTUAL continuation
outcome laws and the absolute payoff is bounded by B. It is not a statement
that close scalar Nash values force close continuation laws.

`cfrDFreshTransportCharge_le_fiberRates` additionally requires, on a supported
OLD observation tag, that the sum of absolute unnormalized atom differences
within that fiber is at most rho times its OLD observation probability. It
bounds the existing computed live charge by:

    childLoss + B * eta + 4 * B * rho

The constants retain the library's L1 convention, without silently inserting
the one-half total-variation normalization. Inactive queries have zero charge;
nonnegative loss/rates justify the common upper bound. No positive minimum
reach, density upper bound or atomwise absolute-continuity premise is used.

`cfrDWeightedTransportLoss_le_fiberRates` integrates this UNIFORM query bound
under the actual private parent seed/history joint law against an arbitrary
unknown opponent. Perfect recall and the existing unilateral density theorem
supply reference support for the actual queries. The argument does NOT remove
an opponent density from an OLD-weighted mean, independently redraw the seed,
or identify a model PBS with the actual opposing posterior.

`freshChainControl_parent_fiber_zero` discharges rho=0 for the constructed two
fresh solves at the SAME cut via `cfrDFreshInformationChain_referenceLaw`.
The typed equality only exposes definitional aliases; it assumes no equality.
`freshChainControl_weightedBudget_le_rate` and
`freshChainControl_biased_rate_security` consume that result with the real
biased finite parent and both fresh solves. Parent bias 1/8, finite outer T,
its inverse-square-root error term, and child tolerances 1/4 and 1/8 remain.
The additional eta premise remains explicit; the budget no longer depends on
the unknown opponent. This is still the coherent final-average construction,
not an identification with the native iteration sampler.

## Positive, negative and boundary controls

`softJoint` retains a rare query of OLD mass 1/100, with a new hidden atom of
mass 1/10000. `soft_fiber_rate` proves rho=1/50 and
`soft_conditional_bound` proves a conditional error at most 1/25.
`soft_actual_bound` retains that bound even when the actual law concentrates
on the rare query. `soft_new_atom` explicitly records zero OLD mass at the new
atom; `soft_no_atom_rate` proves no finite atom-relative rate can hold there.
Thus the fiber hypothesis is not hidden atomwise absolute continuity.

The inherited density counterexample, disappearing-NEW query, absent-OLD
query and zero-continuation-fuel controls are preserved. In particular,
`density_cannot_be_dropped` still rejects replacing an actual opposing law by
an unweighted OLD-model average.

## Remaining work, not acceptance by renaming

M06 is NOT complete. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending; frozen coverage.json statuses are unchanged.
This checkpoint does not claim that eta tends to zero as fresh budgets grow.
The uniform all-history continuation-rate hypothesis must be discharged or
replaced by an appropriate proved one-sided value guarantee for the solver.

For the native sampler, inspect `PBSCarriedDepthFirstHit.lean`: its first-exit
law retains the private memory, carried model and unexecuted suffix. Existing
first-exit expectation identities and charges are NOT by themselves vanishing
rates. They need source-specific control of those actual suffix discrepancies.
Same-cut reference invariance does not establish invariance for independent
later carried-PBS solves. Do not feed this example into CarriedResolveStepBounds
as an unconditional recursive guarantee. Preserve the printed/corrected
Theorem 3 distinction and the real-proof/executable-numerical boundary.

Resume by checking the source workflows above, recording observed final
results, then addressing these algorithm-level obligations. Do not reapply an
old ZIP, rebuild accepted predecessors from scratch, or infer acceptance from
this document's existence.
