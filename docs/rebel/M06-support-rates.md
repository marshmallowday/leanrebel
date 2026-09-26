# M06 — support-specific actual/model execution rates

## Scope and source locator

This is a project-derived dependency for ROADMAP M06 and its pending
SEARCH-ERROR / SAFE-THEOREM3 support interface. It is not a transcription or
acceptance of a paper theorem. It refines the executed opponent/model transport
slice without altering the actual event/native-gap integration. Original
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.

## Why full source variation is too expensive for this obligation

An actual incoming point mass can be supported by a stored mixed PBS and still
have large atomVariation from that PBS. Such a discrepancy need not be a
support failure. We retain the earlier variation bound for value/conditional
transport and derive a smaller bound for posterior containment only.

Write D(a,b) = a({x : x is not in support(b)}), and let K,L be the actual and
model one-step kernels. The finite-law lemma proves

    D(a.bind K, b.bind L) <= D(a,b) + E[x~a] D(K(x),L(x)).

Pointwise, a missing model output requires either a missing model input or
missing model kernel support at that input. If both supports contain the
input/output, support_bind puts the output in the bound model law. This uses
only finite-support probability laws: no Fintype instance on either carrier
is needed. The actual-input expectation cannot be replaced by the model law.

Iterate the lemma along canonical runBehavioralFrom execution. The input to
each leakage term is the actual prefix law. The resulting allowance equals
incoming unsupported mass plus executionSupportCharge. Zero fuel retains the
incoming defect. Absorbing equal kernels have zero leakage. The two profiles
remain fixed over this finite continuation; independently re-solving at each
public checkpoint is a separate composition problem.

## Carried belief interface and premises

The model profile is chosen; the actual profile is
Profile.update unknown who (chosen who). The unknown opponent remains an
arbitrary fixed legal information-local profile, not a policy that sees an
iteration seed. The stored belief is advanced only with chosen.

The event is failure to find a genuine carriedBeliefUpdate posterior whose
support contains the actual resulting history. Both an impossible public
observation and an absent hidden history in an otherwise possible public
fiber remain failures. The existing contains_of_supported theorem embeds
this failure event in the final model-unsupported set. Therefore its actual
probability is at most carriedOpponentSupportCharge, which is proved no larger
than the earlier carriedOpponentModelCharge on a finite history carrier.

The explicit zero-charge theorem assumes only incoming support inclusion and
one-step execution support inclusion at every history, not equality of laws,
profiles or posteriors. These are sufficient primitive premises, not claims
that arbitrary independent re-solving satisfies them. The unrestricted rate
retains their failures numerically. No event probability is divided out, no
mass floor is imposed, and no false posterior is constructed off support.

## Consumers and adversarial review

pbsOpponentSupport_live uses the existing finiteBudgetControlBelief and the
computed information-set CFR child with budget 1/8, one live execution step,
an arbitrary legal unknown opponent and a supported actual starting history.
The initial support charge vanishes even though its actual law is a point
mass rather than a replacement draw from the stored PBS.

The canonical FinDist controls retain actual weights (1/4,3/4). A model with
weights (1/2,1/2) has zero support loss but atomVariation 1/2. For the retain
actual kernel and collapse-to-1 model kernel, actual-prefix support leakage
is 1/4; weighting by a pure-at-1 model prefix instead gives zero. The strict
negative theorem rules out that incorrect replacement. These are finite-law
diagnostics, not fabricated CFR regret tables.

Five additional exact-rational Python tests cover 16,384 two-state cases of
the finite-horizon support bound and its comparison with variation, unequal
supported laws/profiles, zero-fuel incoming loss, wrong-prefix undercharging,
and rare/impossible model outcomes (including mass 1/1,000,003). All earlier
tests remain. Python arithmetic does not certify the Lean declarations.

## Validation and unchanged trust surface

New code extends three already imported and audited modules; no new module is
hidden behind missing imports. The unchanged target has 110 modules; global
ReBeL discovery has 253. Dependency pins, workflows, original source ledgers,
architecture expectations and auditor implementations are unchanged. No
placeholder, custom axiom, native proof shortcut or warning suppression is
introduced. New Lean results remain candidates until exact-source compiler,
normal/slow lint and transitive-axiom output have actually been read.

See M06-support-rates-validation.md for checkpoints, source/artifact hashes and
remaining checks. Full M06 safety additionally needs quantitative primitive
leakage rates for the real recursive schedule, changed-PBS native/value rates,
and CarriedResolveStepBounds. The finite-T residual, public conditional event
mass and actual/model distinctions are preserved throughout.
