# M06 coupled trunk trace checkpoint

The generic numerical driver now constructs the simultaneous trunk-only
recurrence, actual oracle response, full legal continuation profile, and its
local regret-matching realization. Unsearched tables remain zero. Local
square-root bounds are proved against the produced score sequence, not against
a separately supplied learner sequence.

This is an intermediate interface: a CFRDResponse contains a continuation and
backed-up scores. It does not yet derive those scores from a single PBS value
vector. Semantic adapters must prove that link; the final regret theorem must
also account for off-path counterfactual continuation improvement. No root
regret conclusion or final Nash result is a response field.

The previous conditional module's initial target run `35453520626` failed on
three proof/parser issues: an already-closed goal, an ambiguous rewrite, and
use of reserved `public` as a binder. Commit `480ca200` fixes them without
changing the statements and imports the module in the mandatory basic audit
root. Its target and this new trace still need exact-source compiler checks.
No milestone or coverage acceptance is asserted here.
