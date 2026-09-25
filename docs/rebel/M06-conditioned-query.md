# M06 execution-conditioned native queries

## Continuity and source

Work branch: `rebel/m06-conditioned-query-20260925`. Planning checkpoint:
`6089d7916192b72577d5e74cb30f70e2d238d2c0`; proof parent:
`3cfc5e0cc27b2574f585a8a8763794ba73d05687` on
`rebel/m06-joint-query-repair-20260925`. Read the actual work-branch head.
All earlier proofs/checkpoints are preserved. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. M06 is NOT complete.
The prior restart note is retained as M06-status-before-conditioned-query.md.

This is a project-level refinement of ROADMAP M06's private retained-iteration
and carried-query source-law boundary, not acceptance of paper Theorem 3.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06-conditioned-query-coverage.json is a candidate record, not a ledger
acceptance transition. No original source row is deleted or promoted.

## Constructed law and proof obligations

Fix the actual canonical full-information CFR solver, finite legal histories
and menus, a TypeBeliefSlice with compatible full joint-history kernels, the
model's own-type law, positive finite iteration count t, and fixed legal
opposing policies. Let P be the PRODUCT of the genuine uniform private
iteration law and the model's own-type law. For tag (n,x), execute the legal
own iterate n against those opponents from slice.kernel(x), retaining the
seed for the entire continuation. The training and execution horizons may
differ. No policy is given access to the retained proof-side tag.

pbsInformationCFRExecutionKernel uses canonical PublicBelief.continuationLaw,
Profile.update and the actual pbsInformationCFRIterate; no payoff matrix,
regret certificate or arbitrary replacement solver is substituted.
pbsInformationCFRTaggedExecution retains (n,x) alongside the resulting history.
The tag marginal is P. Its history marginal is exactly canonical execution
of the existing CFR average from slice.mixture(own), by the already proved
pbsInformationCFR_sampling_law. Entire joint-history kernels are preserved.
This marginal-law equality alone is NOT a safety theorem.

For an event E in the complete tagged execution with actual mass p>0,
pbsInformationCFRConditionedQuery conditions that execution, then projects
to the retained tag. Events may depend jointly on seed, type and history;
independence after selection is never assumed. The constructor requires an
actual supported point in E, which entails p>0. An impossible event has no
such constructor witness. Off-path conditional kernels still exist, but
conditioning cannot invent positive mass at an originally absent type.

FinDistSelection proves, using only canonical finite-support expectation and
condOn APIs, that selection amplifies a nonnegative tag observable by at most
1/p. Applying this to atom indicators gives Q(a) <= P(a)/p, hence support
containment and the actual ratio r(a)=Q(a)/P(a), with Q=P*r and r<=1/p on
model support. Zero model atoms have zero selected mass and ratio zero.
This derives the density contract instead of assuming it. Nonnegativity is
essential: a signed-loss Python negative control rejects dropping it.

The native gap g(n,x) still compares the own iterate n to the SAME computed
average opponent's conditional best response, at the ORIGINAL fixed kernels.
The previous native mean theorem gives E_P |g| <= B_T. The new theorem derives

    E_Q |g| <= B_T / p,        p * E_Q |g| <= B_T.

The budget specialization uses the computed positive iteration count and gives
E_Q |g| <= error/p. No small-gap premise, input equilibrium, learner convergence,
minimum type probability or minimum event probability is supplied. Finite-T
error remains present even for exact value oracles. Rare-event amplification
is explicit; these statements do not imply a uniform conditional bound.

The execution opponents may be arbitrary fixed legal policies; the gap's
comparison opponent remains the solver's computed average. Confusing these
opponents would silently strengthen the theorem and is explicitly excluded.
Selecting a public-history event is permitted, but identifying its posterior
with a fresh independently re-solved carried PBS and transferring conditional
value gaps to changed kernels/opponents are still separate obligations.

## Positive and adversarial controls

Examples.PBSConditionedNativeGap specializes to the genuine HiddenTypes
full-AOH solver at computed budget 1/8 and a one-step canonical continuation,
with arbitrary fixed legal opponents. It supplies a real nonempty execution
witness for the certain event and recovers the actual native bound. This is
a formal instance, not a numerical execution of real-valued budget code.

A separate finite-law diagnostic starts with independent uniform Fin 2 seed
and type, emits the type through a nonconstant deterministic kernel, and
selects equality of emitted outcome and retained seed. The event has mass
1/2 and its derived query is exactly the existing diagonal law. Both marginal
laws remain uniform, but diagonal nonnegative loss changes from mean 1/2 to
mean 1. Thus the factor 1/p=2 is sharp and cannot be replaced by one. The empty
event is separately rejected. These are law-level diagnostics, NOT purported
solver-generated CFR gap tables and NOT refutations of unrelated guarantees.

## Actual predecessor validation, not new-source evidence

Exact 3cfc5e0 targeted run 36149297405, job 108118391960, was inspected with
all steps SUCCESS: target compilation, the strengthened 104-module configured
normal/slow lint and all 1,626 targeted declaration axiom checks. Artifact
10871926060 was downloaded through the GitHub plugin. ZIP SHA256:
54b3a3a8012359cfd2cf82d14ccc4ba9becdb92e264a6566dcdca05235523dec;
log SHA256: 2eb79622ac550d39cc1159c542e69d4f2c5776b4690e78fb341b9eda06522de5.
All three new predecessor joint theorems and the live control have complete
axiom sets [propext, Classical.choice, Quot.sound]. Its two new joint modules
contributed 3 and 15 audited declarations. The actual log ends with
EXACT_LEAF_VALIDATION_PASS modules=104. This closes the prior targeted
compiler/lint repair loop; it is not validation of the present additions.

Predecessor all-ReBeL 36149297460 / 108118775734 was still in its global audit
when inspected; all preceding static, source, ledger and rational-runtime steps
passed. Full CI 36149297382 / 108118771741 must also be read. Do not replace
new-source validation with either predecessor result. The old e651 native
global evidence remains separately valid and unchanged.

## Current checkpoint gate

All three new modules are added to the analytic umbrella, M06 compiler targets
and supplemental auditor (now 107 modules). Global discovery finds 251 ReBeL
modules; discovery is not compilation. No warning, lint, axiom, architecture,
runtime, dependency or source-identity check is disabled. The ordinary root
GameTheory.lean remains unchanged.

The five new exact rational/wiring Python tests were executed with all prior
tests: 92 tests SUCCESS, warnings treated as errors. Test log SHA256:
4991951f23e294830e69a5ec2519178faff7100ac1c2bf1ab9026ab6da2b4880.
Ledger/inventory structural checks retain all 3,054 inherited items and statuses.
Prepared source bytes were matched to plugin-created blob hashes. These local
checks are not Lean execution; no local Lean run is claimed.

New-source compilation, normal/slow lint, complete transitive axioms, all-ReBeL
and full CI are PENDING this push. Read exact-head diagnostics and repair them
without weakening any statement or gate. All GitHub access and writes use the
GitHub plugin; offline source tests use its downloaded snapshot, without local
Git operations or direct GitHub HTTP.

Remaining M06 work includes actual public-carried-PBS identification, quantitative
first-exit/support and event rates, independently changing opponents/PBS native
and late rates, recursive re-solving safety and CarriedResolveStepBounds.
Do not substitute this native conditional mean result for those obligations,
or infer learner-independent Theorem 3 from learner convergence.
