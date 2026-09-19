# M06 child sampling: carried belief and adversarial controls

The coupled child-resolver/oracle source `50953465ef67233f96217bfca353e8074bff0d06`
passed target run `35476596169`, job `105986817394`. Full exact-source lint,
architecture, runtime and transitive-axiom gates are separate and may still
be running. No milestone acceptance follows from target success alone.

The child resolver now connects to privateCarriedResolveStep: the new private
profile is retained and the model belief is updated from the carried joint
past, not replayed from the initial state. Projecting the history yields the
same constructed virtual continuation law against every fixed opponent.

Examples/CFRDChildControl supplies two distinct Boolean child policies in the
canonical two-stage HiddenTypes protocol. Only the first strategic round is
searched; the second remains live. Exact reference prediction accuracy and
complete-history realization are instantiated for every positive parent T and
every opposing behavioral policy. The control deliberately does not assert
counterfactual optimality of its zero-own-reach averaging fallback.

At an explicit legal live history the two child policies have actual returns
zero and two against a fixed legal opponent. The fair child resolver returns
one, whereas replacing its table by the constant-false resolver returns zero.
Thus the proof surface rejects a mismatch between the policies used for value
backup and the table actually sampled. These new controls require their own
exact-SHA compiler result; they are not validated by the preceding target run.

The general recursive child-solver and off-path completion obligations remain
open. These controls validate the law-preserving adapter and its boundaries,
not M06 completion. No source coverage row is promoted here.
