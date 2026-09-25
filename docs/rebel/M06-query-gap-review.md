# M06 query-weighted conditional-error slice

## Starting point and predecessor repair

Work branch: `rebel/m06-query-gap-20260925`.
Parent source: `fa03b39e497e4d9802d978caab052ce2802ccdc1` on
`rebel/m06-conditional-gap-20260925`. Main remains at the accepted M05
checkpoint; all earlier branches are preserved.

The parent removes two redundant `simp` tactics from the canonical exact-Nash
control, and no theorem or audit condition. The observed failed predecessor
was `e58eff73bcff5f8a67ccb1745f49bf9e762ba398`, targeted run
`36122926779`, job `108032492682`. Parent targeted run `36124896554`,
job `108038627933`, has now PASSED the declared M06 compilation step;
its separate lint/axiom step was still in progress when last inspected.
Independent parent ReBeL checks are run `36124896574`. Neither unfinished
run nor any parent result is a successful exact-source test of this addition.

The parent source was exported only through the GitHub plugin, artifact
`10859251534`; ZIP SHA256
`36ede2aa837ffaeb5523c57dc50cf072b451e6e60e15b5333dfe87f6ab46e89e`,
source TAR SHA256
`c2246df3ec55665e734b7880ee443ea0b78bca62a48646c89a032d556ca224f3`.
Both hashes and the embedded commit were checked. On that exact export,
all 83 Python tests and ledger/inventory structure checks passed. These are
not Lean compilation or proof acceptance. No local git or direct GitHub
network access was used.

## Statement and proof boundary

This is a project-level refinement of the existing M06 conditional-loss
interface, not a proof of a previously pending full paper theorem.
At one fixed canonical `TypeBeliefSlice`, let g(type) be that profile's
CURRENT-opponent Eq. (1) best-response value minus its self-play conditional
payoff. Perfect recall proves g >= 0. The existing remembered-type global
deviation theorem already proves E_own[g] <= epsilon from actual root
approximate Nash. The new result makes the absolute norm explicit:

    E_own[|g|] <= epsilon.

For a different probability law of queried types, supplied with the exact
atom identity query(type) = own(type) * ratio(type), and a cap
ratio(type) <= C on own support, C >= 0, the new theorem derives

    E_query[|g|] <= C * epsilon.

The proof uses the established `informationReweight_expect`, expectation
monotonicity and the own-law mean theorem. No minimal atom probability is
assumed or divided by. The density identity excludes new queries at absent
types; it does not set their continuation kernels or true values to zero.
The query law changes while the slice, root game and opponents remain fixed.
This is not the same assertion as a uniform conditional oracle error, whose
existing normalized reweighting theorem preserves the uniform constant.

Both actual finite-T and requested-positive-budget information-set CFR
specializations derive their own Nash premises. The finite-T coefficient is
`pbsRootCFRBound`; it is not erased at zero oracle error. The bounded density
is still an explicit condition on the query source, not something inferred
from Nash or asserted for the native/late-training sampler.

## Controls and audit coverage

The live HiddenTypes one-eighth-budget solve now proves a mean absolute
gap under its actual full-AOH own law using density one, with no supported
atom or minimum-mass premise. It preserves the joint-law slice factory and
legal information-local policy construction.

The rare-type example is strengthened with an actual normalized FinDist
prior (1/4, 3/4), a query concentrated on type zero and exact density (4, 0).
A legal finite zero-sum type-plan game is genuinely 1/4-Nash, has own-law
mean conditional gap 1/4, and query mean gap one. Thus dropping the density
factor would be false even for a dominated query. Conditional optima are
connected to the canonical `TypeGame.infoValue`, not an arbitrary error
array. The absent-query control proves no density can move a pure type-one
prior to a pure type-zero query. Earlier changed-opponent, rare-type and
absent-type adversaries are unchanged.

The additions are in the two already imported/audited conditional-value
modules. No module, declaration, target, fallback, negative control,
dependency pin, linter, axiom allowance or architecture gate is removed.
All new declarations are therefore in the existing umbrella, targeted
compile, explicit exact-leaf audit and global ReBeL audit consumers.

## Exact-source validation and remaining work

At this implementation commit the new source is pending its OWN GitHub
Actions build, normal/slow lint and transitive axiom audit. Inspect exact
branch-head run identities before acceptance; parent compilation is not
substituted for this source. Preserve the successful repair checkpoint.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
In particular the proof does not provide native/late query density caps,
changing-slice or independently changed-opponent conditional vector rates,
first-exit control, or `CarriedResolveStepBounds`. Independently re-solved
carried-PBS safety and the printed/corrected Theorem 3 obligations remain.
M06 is incomplete. These restricted mean-error statements do not weaken
or discharge those original obligations.
