# M06: sampling comparison through a complete finite schedule

## Confirmed predecessor

The exact source 6c541fca806b1443c5980d782ca8d32db58dc373 passed:

- M06 target run35834987027/job107096169276.
- Full CI run35834986816/job107096441587, including build, lint, architecture and cleanliness.
- ReBeL run35834987171/job107096567710, including compiler, lint, transitive axioms and runtime.

The targeted log reports EXACT_LEAF_AXIOM_AUDIT_PASS declarations=781 and
EXACT_LEAF_VALIDATION_PASS modules=64. The three preceding new modules own
3 + 26 + 21 = 50 declarations including generated auxiliaries; there are
fourteen named theorem controls. The targeted artifact is10739395664 with
SHA256546b667e3bd0a8e53dbc8efabc69f2758f1ca2b4965f6cf3fd5cfe3a29d9c65f.
Do not redo that validated single-step and arbitrary-identical-future slice.

## New dependency-closed slice

FinDistSequentialError defines finite monadic kernel composition and the
sum of event probabilities under the FIRST execution's successive laws.
For N_k = native and H_k = comparison, rho_0 = rho and
rho_(k+1) = rho_k.bind N_k, the theorem states, for any finite final kernel F
and any globally bounded observable |V| <= B,

    |E[rho N_0 ... N_(m-1) F] V - E[rho H_0 ... H_(m-1) F] V|
      <= 2 B sum_k rho_k(E_k).

The proof replaces the suffix first: the induction runs at rho.bind N_0,
then the first-stage event estimate uses the already compared suffix as its
common final kernel. Consequently no compared-prefix law is substituted for
rho_k. Events and kernels may read every component of the state. The sum is
an expected visit count, not a probability of an event union.

PBSCarriedRecursion instantiates this result using the EXISTING
carriedMemoryStep and the native-history-first full-state disintegration.
PBSCarriedCFRParameters keeps training fuel, execution fuel and strictly
positive iteration counts separate; different stages may use different counts.
pbsCarriedCFRSequence_execute proves the new full-state expression is exactly
executeCarriedResolves before its final selected continuation. The error result
therefore applies to the canonical finite runner, not a replacement game model.
The append theorem retains the entire native checkpoint law for the suffix.

The history-first comparator is ANALYSIS-ONLY. It may depend on hidden history
and the unknown opponent through native conditional disintegration. It retains
selected profiles together with their own propagated MODEL posteriors. Neither
these conditionals nor their correlations are replaced by the stored model law.
No CarriedResolveStepBounds, final safety or individual-iterate Nash premise is
supplied. No support hypothesis is imposed on the actual incoming state law.

## Controls and semantic review

Examples.PBSCarriedRecursion uses the previously tested hidden-type schedule,
with iteration counts two and three, and proves equality to that exact schedule.
A factual supported live root tests storage of the full joint next state.
The full two-stage error is checked after arbitrary state-reading future kernels
and for the original executeCarriedResolves interface.

A separate two-state example starts at false and moves to true before the
second stage. Every event has initial-law mass zero, but the second event has
actual forward mass one and the observable error is exactly two. It guards
against charging all stages at the initial distribution. This is a counterexample
to an invalid composition shortcut, NOT to source Theorem3.

## Source correspondence and unresolved obligations

Source: main Theorem3, supplement G, printed pages21-22; ROADMAP M06 and
M06-carried-iterations.md. This is supplemental proof-depth evidence, not a
promotion of the frozen source rows. The child is still native full-root CFR;
source-dependent decay of the exceptional mass is not inferred from this sum.

| Original obligation | Progress in this slice | Still needed |
| --- | --- | --- |
| SEARCH-FRONTIER | Canonical scheduled transitions retained | Source acceptance review |
| SEARCH-CFRD | Same native carried solver composed at every stage | Recursive depth-limited child/oracle connection |
| SEARCH-ERROR | Complete finite-schedule bound at actual forward laws | Source-dependent model drift and exceptional-mass rate |
| SAFE-THEOREM3 | Exact existing-runner identity and full-state comparison | Joint parent-oracle and recursive security proof |

Preserve finite outer T and nonzero prediction/child errors. The printed
formula and corrected finite-iteration formula remain separate. Neither
unrestricted source safety nor executable numeric refinement is claimed.

## Current verification

The new three-module slice is included in the analytic root, M06 target list
and supplemental normal/slow-lint and axiom auditor. This source checkpoint
requires its OWN exact-SHA CI; predecessor success is not inherited as proof
of the new declarations. See STATUS.md and the actual branch HEAD/check runs.
