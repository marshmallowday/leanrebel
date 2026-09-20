# M06 conditional completion: reconciliation and value invariance

Active work branch: `rebel/m06-joint-completion-20260920`.
The initial source was `cd2e0f271dc8c55a3df66709ce5016a9c3c6a580`, whose
M06 target run `35478943461` / job `105993069826` succeeded.
The first conditional-deviation checkpoint was saved as
`8a3a5773b5c426d67e0b77326b2840a568d8728b` on this isolated branch.

The original resume branch advanced concurrently to
`b5978ef674f46f02c4b39785b033dd42bdc26ddf`, introducing CFRDCompletedLeaf
and joint zero-reach controls. A non-fast-forward update was rejected and was
not forced. This reconciliation keeps both histories, imports that new source
unchanged, and uses its canonical deviation-continuation theorem. The duplicate
local declaration is removed rather than introducing parallel definitions.

CFRDConditionalCompletion now adds reusable conditional-payoff equalities and
an attained-infostate-value equality. All complete behavioral deviations have
the same payoff against the completed opponents when their original own
reaches are nonzero on the conditional kernel. Taking the attained maximum
therefore preserves the value as well. The focal player's reach can be zero;
no Nash premise is needed for this equality. Actual-policy payoff preservation
separately requires positive original own reach for every player.

The joint all-type optimality construction and positive/negative controls in
b5978ef6 are inherited work, not counted again as new local proofs. Their exact
source CI and this merged source's CI must be inspected independently.

Remaining M06 obligations: derive kernel support/reach alignment for the actual
counterfactual queries, construct fresh recursive child solves with the needed
continuation quality, and connect them to the corrected finite-T Theorem 3.
This checkpoint changes no coverage status, axiom allowance, theorem premise,
or negative test. Compiler/lint/architecture/axiom acceptance remains pending.
