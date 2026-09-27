# M06 dependency: changed compatible kernels with fixed opposing policies

## Scope and mathematical claim

This is a project dependency for ROADMAP M06, not acceptance of a paper theorem.
The parent is 372c9c94261f5e553ff9ce619816b7ca9cf7493b, preserving the latest
0285093 checkpoint and the exact-source 51d5 noisy-parent proof. M06 remains
incomplete. No library pin, execution semantics, architecture budget or prior
acceptance gate is changed.

Let K and L be two complete conditional laws on the same canonical protocol
history type. They come from compatible TypeBeliefSlice kernels; their public
trace indices and type domains may differ. Let d be FinDist.atomVariation K L,
the full L1 atom discrepancy, not half that quantity and not an old-support-only
sum. Fix the payoff, horizon, opponent profile and the own response policy.
For a payoff bounded by B at every physical history, the canonical continuation
expectation is bounded by B. Its change under K versus L is at most B*d.
Uniform control of every legal response also bounds the attained Eq. (1)
conditional optimum by B*d. The proof uses the two actual maximizing legal
responses supplied by infoValue_isGreatest and their opposite-side domination;
it does not assume an optimal-value stability certificate.

The conditional gap is optimum minus the chosen own-policy payoff. Its signed
change in either direction is bounded in absolute value by 2*B*d. Hence the
fresh absolute gap is at most the old absolute gap plus 2*B*d. These statements
retain off-path compatible type kernels, ties between maximizers and new-only
atoms. No on-path or positive-own-mass assumption is required.

## Connection to the actual constructed noisy depth parent

PBSDepthKernelGap applies that estimate to pbsInformationDepthCFR iterates,
using the exact pbsRootDepthBudget already derived by the constructed solver.
The sampled seed/type pair comes from the actual tagged execution conditioned
on an explicit positive event. Fresh compatible slices may depend on the
selected seed, and retag explicitly maps each selected pair to its fresh type.
The result is

    E_query |fresh gap| <= depthBudget / execution.probOf event
                           + 2*B*E_query d(old kernel, selected fresh kernel).

The native budget pays the actual event reciprocal. The kernel term is already
averaged under the conditioned query; it is not divided by the event mass a
second time. The pair distribution stays joint, not the product of newly taken
marginals. The comparison opponent remains the same computed average parent
profile. The arbitrary fixed execution opponent does not replace it in the
gap definition. Horizon, payoff, finite-T residual, numerical-error and positive
child-loss terms are all retained.

## Controls and boundaries

The Lean controls use real legal hidden-type protocol roots with the same
public cut and coarse own type but opposite hidden opposing bits. At zero
continuation fuel a bounded observable has values -1 and +1. The resulting
actual conditional optima differ, and the full kernel discrepancy is exactly
2, including the new-only history. A separate example uses the actual noisy
two-iterate depth parent at a four-root joint PBS, then changes to a pure-root
belief using completed full-AOH slices. Absent own types keep their physical
off-path completions. The public event is certain in this integration control;
the inherited impossible-event control still prevents conditioning on mass 0.

Eight independent Fraction fixtures include 4,050 exhaustive two-history/
two-action cases, the necessary factor 2 for gap changes, new-only atoms,
correlated query pairing, explicit type readout, and a counterexample to
changing opposing policies while claiming only a kernel cost. Arithmetic is
not Lean validation.

Fresh slices/readout are explicit compatible data. This theorem does NOT prove
that they are the posteriors of a particular recursive resolver. It does NOT
make d small; different public cuts can have disjoint supports and d=2. It does
NOT compare independently re-solved opposing policies, establish unrestricted
primitive support smallness, or construct signed CarriedResolveStepBounds.
Those source-specific identifications/rates and late-value transport remain
required. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. Learner convergence is not test-time safety.

## Validation ownership

The owning M06-kernel-value-transport-coverage.json lists exact declarations,
source blobs, controls, consumers and pending CI. The existing root, target
manifest and exact-source auditor only gain the three modules. The expected
counts are 116 targeted module audits and 259 repository-wide module audits.
Do not infer their success from the older 51d5 target acceptance.
