# M04 constructed root-decomposition checkpoint

This is a partial M04 development checkpoint, not milestone acceptance.

## Preserved, inspected progress

- 507f81dd84e6ef94b4d275581fc3f86a886b30fa: full CI run 35305351333,
  job 105476302968 succeeded, including build, Phase 1/2/3 audits, complete
  library lint and tracked-file cleanliness. This repairs the prior formatting
  failure without modifying any acceptance gate.
- 9f1cb3ec08069e1779608795d81ce420dd082783: ReBeL run 35306277156
  exposed two dependent-type elaboration errors. The fixes preserve statements.
- 5810e9e3cd4c2623962e51e550d7d42f6d8b8fa4: run 35306822391,
  job 105480607305 compiled ChronologicalLocality, its full-game example and
  PolicyPatching. Public-root import then exposed a collision of automatically
  named local equality instances. This checkpoint names the new instance
  uniquely; it does not hide either module from public-root/lint/axiom consumers.

## Actual construction

RootDecomposition.scheduled_root_gain uses the exhaustive scheduledSites list.
A list induction carries a finite set of already replaced own-information
states. Every step is a canonical Profile.update with BehavioralPolicy.withLaw.
Continuation locality covers strictly earlier and distinct equal-depth sites.
All earlier decisions are proved covered before the next scheduled site, so
its coefficient is the fixed deviation policy's actual own reach. The remaining
local regret is that of the original profile, not of a convenient hybrid.
The final patch induces the full behavioral deviation's actual history law.

The auxiliary partial_root_gain_sum has only structural enumeration premises:
no supplied hgain, regret estimate, equilibrium certificate or solver conclusion.
The public scheduled theorem discharges every enumeration premise from the
actual finite full-history schedule and perfect recall. It quantifies over
all behavioral deviations, including off-path decisions, and all payoff
observables. The genuine two-stage hidden-type example and zero-horizon case
consume the same generic theorem.

## Acceptance still pending

The new root source must pass its own Actions compiler/lint/axiom and full CI
results. Source declarations alone are not accepted Lean evidence. The ledger
remains unchanged at this checkpoint. Remaining M04 work includes the coupled
CFR iteration, uniform finite-T bound, own-reach averaging and independent-seed
realization, canonical zero-sum Nash bridge, rational execution/refinement and
independent best-response tests. Do not count this root identity as the complete
solver or weaken these obligations. All remote changes use the GitHub plugin.
