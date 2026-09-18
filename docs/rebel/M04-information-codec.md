# M04 history and information codec checkpoint

The recovery source `7ada1350e451a439267362d70797edc075c063d3` passed the unchanged
static architecture audit, all 46 Python regressions and the actual rational
Lean runtime check (T=0/1/2, 1024 pure responses per player).
ReBeL run `35355631712`, job `105634170923`, artifact `10551238277`.
`RationalAverage` compiled successfully in that run, completing compilation of
the general arithmetic -> evaluation -> reach -> counterfactual -> iteration ->
averaged-output Nash chain. Normal/slow lint and the transitive axiom audit
were not reached because `Examples/RationalCodec.lean:33` had an ambiguous
unqualified `terminal` name. This checkpoint supplies its direct `not_false`
proof rather than changing the game or dropping the condition.

The new `Examples/RationalInformation.lean` proves exact active-information
encoding: decode/encode inverses, equality of the active information partitions,
coverage of all canonical active histories, realizability of every active key,
and a Boolean/legal-menu equivalence. Own-action memory is retained. No claim
of injective terminal-information encoding is made: the runtime idle key
intentionally has a singleton choice and can represent several terminal AOHs.

This new checkpoint requires its own build, lint and transitive axiom results.
The runtime solver still needs the commuting evaluation/reach/update connection
through this concrete Row/Site encoding. A history bijection and an information
bijection alone do not prove the full solver refinement. M04 remains open;
original ledger obligations and M03 evidence are unchanged.
