# M06 factual posterior to reference-query bridge

CFRDFactualQuery connects the constructed factual child posterior to the
actual private/live unilateral-reference conditional. The proof first removes
redundant public/live conditioning on a supported full-AOH fiber, then uses
the proved information-local density to identify the factual and reference
conditionals. It does not equate arbitrary off-support fallbacks.

The module also proves that the constructed child's complete factual and
counterfactual query packet is exactly the trunk's packet. Equilibrium
continuation choices cannot retroactively change the query.

Parent source 9fa128af8f18bd5acad07f45de17c588228b4420 compiled the general
CFRDFactualChild module in run 35492713268/job 106030281617. That target run
failed only on a missing decidability instance in the concrete live-query
control. The control now uses classical locally; its statement is unchanged.
The added kernel identity and query-packet controls consume these new bridges.

This code requires new exact-SHA compiler, normal/slow lint and transitive
axiom validation. Its target and analytic imports are registered. The factual
child and boundary controls remain mandatory. No M06 acceptance is claimed.

Next reconstruct the child posterior as the mixture of the actual encoded
reference type kernels, supply each factual type's support, and transfer the
constructed child Nash theorem to the reference-table leaf contract. Exact
reference solving is still separate from finite-T recursive CFR and safety.
