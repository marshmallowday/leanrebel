# M06 constructed public-state response splice

Work branch: `rebel/m06-public-splice-20260920`.
Inherited verified source: 8ab23b4bb20349df616736d9b5c6d980f3e7eb41.
The present changes require their own exact-source verification.

## Construction and semantic scope

CFRDPublicSplice selects complete legal behavioral responses by the public
history reconstructed from each player's full AOH prefix at a fixed cut.
It proves persistence on all legal descendants, equality of the full joint
continuation law, equality over joint public beliefs, and equality against
every fixed unknown opponent. There is no positive-reach assumption in these
splicing identities and no replacement of a joint law by private marginals.

CFRDPublicResponse computes the response table using the existing finite
conditional best-response optimizer. Optional entries do not require a
probability law at impossible public histories. Missing entries use an
explicit legal fallback. For present entries, the public splice DERIVES the
local-response agreement previously assumed by CFRDCompletedContract.

cfrDPublicResponseCompletion_leafOptimal derives the existing zero-loss
CFRDLeafOptimal contract after joint zero-own-reach completion. Its queries
premise identifies actual typed kernels, factual support, table entries and
canonical PBS Nash; it no longer assumes agreement with a supplied completion
policy. cfrDReference_live_rootDepth derives exact cut depth from supported
live reference sampling, excluding early terminal absorption.

This is full-AOH, finite-history/action best-response semantics. It is not an
executable inexpensive solver, a universal off-support posterior, or a proof
that finite-T child CFR already satisfies exact Nash at every conditional type.
Actual query games, their Nash construction and finite-T recursive child loss
remain separate M06 obligations.

## Controls and failures retained

The five HiddenTypes controls exercise actual different second-round draws
at distinct public roots, all private type pairs, cut-prefix retention after
new public signals, rejection of a latest-public-state selector, and full
continuation-law equality against arbitrary unknown opponents.

Initial source 1ccf7d1e failed target run 35488807141/job 106019977658 because
`public` was used as a local identifier, colliding with Lean syntax. It is
renamed to rootPublic without changing any theorem statement. The downloaded
compiler artifact is 10598079341. No lint or axiom restriction is disabled.

The candidate's 76 existing Python tests and coverage/inventory structural
checks pass after registering all modules. These are not Lean compilation.
The unchanged original coverage parent obligations remain pending; no M06
acceptance, integration into main, or complete Theorem 3 claim is made.
