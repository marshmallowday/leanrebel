# M06 parent-query sampling checks

The parent lint repair `2f4037460bf95104c723f6cdba87ddc2ad9a8227` is now
confirmed green in full CI run `35578223118`, job `106264815082`: build,
inventory, all three architecture gates, complete public-library lint and
tracked-file cleanliness succeeded. Its M06 targeted run `35578223051` also
succeeded. Its separate transitive-axiom run `35578223045` was still running
when inspected; the main CI does not replace that audit.

The next source `d82847c8cc489ac31083fba36173314431e944bf` was validated as
a failing candidate, not silently accepted. Targeted run `35579856395`, job
`106269958842` found unused section instances only on
`cfrDInformationQuery_possible`. ReBeL run `35579856269`, job `106269958273`
found a single 101-unit line. This checkpoint explicitly omits the unused
instances for that theorem and wraps that line. No linter was disabled.

Concrete hidden-type controls now witness an inhabited factual private/live
query for each player, apply the query-law theorem at positive continuation
fuel against arbitrary fixed opponents, and check the zero-fuel identity.
Earlier diagonal-index and zero-model-mass counterexamples remain unchanged.
This changed source requires its own CI, lint and axiom audit.

The zero-factual-mass response-completion branch and its common leaf consumer
are the next slice. Original M06 coverage remains pending; these controls do
not establish recursive carried-PBS safety or Theorem 3.
