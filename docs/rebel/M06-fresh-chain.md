# M06 — finite fresh chains and noisy-parent root security

## Scope and original source

The source obligations remain main Theorem 3 and supplemental G pp21-22, with
locators and the printed/corrected distinction preserved in the original ledger
and M06-fresh-envelope.md. This is a derived fixed-cut intermediate theorem,
not unrestricted later carried-PBS independent re-solving or full M06 acceptance.
See M06-fresh-chain-validation.md for exact source, compiler loop and CI evidence.

## Computation, not a supplied solver certificate

cfrDFreshInformationChain recurses on a finite natural-number stage count.
Stage zero returns the legal input profile. Each successor actually invokes
cfrDInformationContinuation on the preceding result, with the specified new
numerical tolerance, including factual public child solving and counterfactual
zero-own-reach completion. It never receives child Nash, local quality, common
reference law, drift smallness or final security as fields of solver data.

The cut and remaining horizon are fixed during this chain. A stage counts a
fresh child computation, not a played action or a later public observation.
Every successor preserves the original unilateral reference prefix; induction
proves cfrDFreshInformationChain_referenceLaw for both players. External calls
pass the automatically generalized model argument; recursive calls inside the
definition use the already bound section parameter, without passing it twice.

## Derivation of the model envelope

On each supported live information query, the signed new-minus-old value change
telescopes when the FULL reference law is unchanged. Taking the positive maximum
over legal histories and then the finite parent family is subadditive. The
finite-sum theorem and its actual-chain consumer give

    D(profile(0), profile(q+1)) <= sum_{n=0}^q D(profile(n), profile(n+1)).

Repeated legal-history representatives do not enlarge this maximum. Zero factual
reach does not remove a reference-supported query; stopped and unsupported
queries are not interpreted as fictitious posterior samples. Equality merely
of observed/marginal laws is insufficient for this telescoping step.

The final actual child supplies CFRDLeafOptimal at its positive loss(q).
The new-versus-old opponent envelope splits into that final child's response
gain plus its conditional model-value change. Thus cfrDFreshChainResolver_envelope
has loss(q) + sum(interSolveDrift), without a caller-supplied envelope, reference
law or final local-quality certificate. Earlier invalid tolerance requests are
not asserted accurate; only final quality is used in this envelope proof.

## Actual private execution and root security

cfrDFreshChainResolver uses the existing private legal-plan draw of the FINAL
computed average. Intermediate solves are computation, not shared seeds or
observations available to the opponent. cfrDFreshChainResolver_tail proves the
complete original-history law, against any fixed unknown behavioral opponent,
at every legal carried state, including off-model or absent-belief states.
This is coherent-plan resolver semantics, not the separate native-CFR-iteration
sampler. In particular no individual CFR iterate is claimed to be Nash.
Zero execution fuel follows the original no-draw stopped branch.

cfrDFreshChain_security consumes the ACTUAL noisy sampled-value parent and this
derived final envelope. For positive finite outer T its original-game security
allowance is exactly

    C_error * predictionError + C_time / sqrt(T)
      + oldChildLoss + finalChildLoss + sum(interSolveDrift).

C_error and C_time are the existing sums of both players' depth constants.
The explicit hypotheses are finite history/action/menu carriers, bounded zero-sum
history payoffs, nonnegative prediction allowance and its pointwise noise contract,
positive old and last-child losses, and NeZero T. Perfect recall is supplied by
the existing full-observation construction. The comparison Nash profile only
names the original game's security value: it is not consumed by the parent,
child chain, resolver or budget computation.

No term is removed by setting prediction error to zero or pretending T is infinite.
The measured drift is still a classical real-valued specification, not a proved
rate or an executable floating-point backend. Larger T does not erase a fixed
unallocated prediction or drift term.

## Canonical positive and hostile controls

Examples.CFRDFreshChain uses the existing hidden-type protocol and both actual
decision stages. Its first fresh loss is 1/4 and its second is 1/8. Controls include
empty-chain identity, twice-recomputed reference preservation and derived local
quality, the original factually absent but reference-supported query, full private
history law at a missing-belief live state, arbitrary unknown behavioral opponents,
and zero-execution-fuel no draw. The root-security control additionally uses
actual parent bias 1/8 and old-child loss 1/4, with both measured drift terms present.

A finite-law negative control has identical Unit-valued observation laws but
opposite hidden conditionals; the attempted telescoping identity becomes 0 = 0 + 1.
This is not itself a protocol-level or source-Theorem3 counterexample. The existing
M05 ValueKink control separately exhibits different equilibrium type-value vectors;
scalar equilibrium accuracy must not be silently substituted for vector stability.

## Registration and original acceptance boundary

Both new modules are appended to the analytic root, all M06 targets and the
supplemental lint/transitive public-private-generated axiom audit. Every old entry
is preserved. The actual audit list was 84, not the earlier prose's 92; it is now 86.
The target list grows from 122 to 124. No workflow, pin, heartbeat, warning policy,
axiom whitelist or prior positive/negative control is changed or removed.

| Original row | Added dependency-closed slice | Still required |
| --- | --- | --- |
| SEARCH-FRONTIER | Existing live/stopped/off-path semantics retained | Full source acceptance review |
| SEARCH-CFRD | Actual finite fresh-chain computation at one retained cut | Later carried-PBS independent re-solving |
| SEARCH-ERROR | Derived finite sum of supported inter-solve drifts | Useful source drift/support/first-exit rates |
| SAFE-THEOREM3 | Actual noisy-parent root security with all drift terms | CarriedResolveStepBounds and complete corrected safety |

All four parent rows remain pending. A finite sum of measured drifts is not a
vanishing-rate theorem. Do not equate modeled PBS with the actual unknown-opponent
posterior, infer learned-network accuracy, erase finite-T terms, or count this
restricted result as the original full theorem. Preserve all accepted M05 evidence.
