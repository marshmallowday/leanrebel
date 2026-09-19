# M06 carried belief after re-solving

CFRDResolveBelief extends the saved resolver execution with the newly selected
private profile and its updated MODEL PBS. Updating starts from the stored
joint belief, executes the selected future model from those histories, then
conditions on the new public observation. It does not replay the new profile
from the original initial state or insert the actual unknown opponent into
the model posterior. Missing model support remains explicit as None.

The public history can only extend the carried public past. Projecting away
the new model/private state gives precisely the existing canonical resolver
outcome law, and hence preserves the previously derived payoff/security
statement. These equalities are proof targets in this compiler checkpoint;
read the resulting exact-SHA CI before treating them as validated evidence.

The public positive/negative controls remain distinct. The fair resolver's
local comparison is supplied for every opposing policy in the live hidden-type
game. The wrong constant resolver is merely legal and public-only: it loses
one unit at an explicit legal continuation history. That negative control does
not claim that a recursively computed CFR-D or equilibrium resolver is unsafe.

General recursive PBS solving and the derivation of its counterfactual
continuation/replacement contract are still required for M06 acceptance.
This is neither a coverage promotion nor a substitute for those obligations.
