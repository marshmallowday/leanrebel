# M06 native re-solving variation — working checkpoint

Active branch: `rebel/m06-native-variation-20260924`, descended from documentation
checkpoint a5e0700f18ddd19e768c0967d29f1802276ecb55. All repository operations
use the GitHub plugin; main and prior proof/review branches are preserved.

## Accepted predecessor, newly confirmed

Proof source a42467929bbedb0f26bd100e5915d5743ec9025d is accepted by its completed
M06 target, supplemental normal/slow lint and transitive public/private axiom
checks (92 modules, 961 declarations), whole-library CI, and source inventory.
The previously pending independent ReBeL run35954274920/job107489146886 also
SUCCEEDED, completed 2026-09-24T04:46:13Z. Its full ReBeL compiler/lint/transitive
axiom step, rational runtime and independently checked pure responses, static
architecture/ledger/inventory, line width, and tracked-file cleanliness passed.
The remote job's exact head_sha is a42467929bbedb0f26bd100e5915d5743ec9025d.
Do not redo that accepted structural recursion or sampling implementation.

## Compiler checkpoints

Planning daf0fcec609d9902beef3b0cd972c6e9476d8c0d recorded accepted source and scope.
Implementation46f8530a247f9422f8331807bde74274c2764c81 added all three modules
and appended them to all three existing consumers (verified diff: 3 additions,
0 deletions in each of root, targets and supplemental audit).
Target35960543695/job107507954833 failed only at the new probability module:
Set.mem_setOf_eq is deprecated under the pinned Lean4.33.1/Mathlib source.
Every old named target, including PBSComposedDepth/PBSRecursiveDepth and their
examples, compiled. The new dependent modules were blocked; the supplemental
audit was skipped, NOT accepted. ReBeL35960543649/job107508129255 independently
stopped at three 101--103-unit lines in CFRDNativeVariation. The successor uses
the current set-membership lemma and wraps those lines; no gate is weakened.

## Actual dependency-closed slice

FinDistTotalVariation constructs half the finite L1 distance on the union of
supports, without demanding a finite whole carrier. It proves 0 <= TV <= 1,
sharp bounded-observable (2 B TV) and event (TV) estimates, same-law zero,
symmetry, contraction by an arbitrary common future kernel, mean variation
under common mixing, and mass outside another law's support <= TV.

CFRDNativeVariation computes each replacement rate from the incumbent residual
history law and one actual fresh resolver draw retained for that residual
horizon. This is independent of payoff and never reads the recursive suffix's
final output. The local value bound uses the existing exact native-step / chosen
profile / propagated PBS identity. A finite maximum over reached full private
states derives CarriedResolveStepBounds without supplying local loss premises.
A sharper budget sums expected variations along actual native forward state
laws and bounds the actual executeCarriedResolves/privateRecursiveResolve loss.
Stopped/zero-fuel stages have zero charge. The actual unknown opposing policy
is preserved by every law and never passed to the resolver as a query input.

The fresh-query coefficient compares two continuation laws on the SAME OLD
unilateral-reference fiber. Its finite maximum includes only supported LIVE
queries, including zero factual own reach; absent fibers are not fictitious
posteriors. It bounds the existing cfrDFreshValueChange and cfrDFreshValueDrift
rather than assuming a value-vector comparison.

pbsRecursiveVariationStages maps numerical schedule records directly to the
accepted pbsRecursiveDepthStage (the actual recursive finite-budget sampler).
No equilibrium or replacement certificate is stored in those records. The
native step bounds and expected-budget transfer apply to that exact stage list.
Missing model PBSs retain the incumbent, with zero variation even off model.

Controls retain the rational nonzero 1/4 variation and sharp 1/2 payoff change,
a 1/2 support defect, canonical hidden-type live solve equality against every
unknown opponent, the actually recomputed finite child's zero-own-reach query,
its derived drift allowance, and the nonzero-noise recursive no-belief fallback.
The accepted exact-Nash replacement counterexample forces positive variation;
Nash error alone therefore does not justify setting this coefficient to zero.

## Acceptance and semantic boundary

The new proof and controls need their own complete exact-source CI. Do not
infer their correctness from ancestor builds or skipped audits. Preserve all
registered targets, normal/slow lint and transitive axiom consumers, the three-
axiom whitelist, warning policy, 100-column gate, dependency/toolchain pins,
adversarial controls and accepted M05 evidence. No theorem input contains its
own conclusion. All new declarations remain in the three registered modules.

These are classical finite real-valued specifications, not numerical runtime or
learned-network accuracy theorems. The variation coefficients are computed
probability comparisons, NOT a proof of the source's useful delta/T rates. The
actual repeated solver's small-variation/first-exit rates and full source safety
remain obligations. Keep model beliefs distinct from actual opposing-play laws.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending until
their full original-source obligations and semantic reviews are satisfied.
