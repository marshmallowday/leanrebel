# M06 constructed PBS-rooted information-set CFR: compiler checkpoint

Continue on rebel/m06-pbs-cfr-20260921; read its actual remote HEAD.
The parent implementation checkpoint b7ef5dd38fd84abdf2018d1dd04f407df4c7ca98
is retained on rebel/m06-pbs-root-20260921 with its independent target run
35547186126/job 106175078370. This commit adds the observation interface and
native rooted-game solver, and registers all three modules in the umbrella,
M06 targets and supplemental transitive-axiom/lint auditor. No gate is removed.

The original inherited source 93b60fbdc3fe6539a7688124baa9be80b86602c1 has now
passed BOTH full repository CI 35545208101/job 106169800893 and full ReBeL
35545208160/job 106169767571. The latter includes compilation, normal/slow
module lint, transitive axiom checks, the independent rational runtime test,
and tracked-file cleanliness. This inherited success is not verification of
the new source. The new source is a compiler checkpoint until its own run passes.

PBSRootProtocol uses the canonical ExecutionProtocol with an actual initial
chance draw from the JOINT law of legal original histories. It retains legal
transition evidence, derives strict history-length rank decrease and an explicit
finite enumeration. An administrative chance step consumes one additional fuel
unit. Terminal sampled roots retain the original stopping rule.

PBSRootInformation has no hidden-root policy argument. Each player receives
only its original public trace and its own information state. The constructor
is then applied to original full AOHs, and the rooted sequence itself is given
the existing full-information adapter. Menus remain information-local and
are proved adequate, including the administrative singleton and terminal cases.

PBSRootCFR instantiates the existing simultaneous information-set CFR recurrence
at a fixed positive iteration count, with own-reach averaging. It supplies
finite histories, finite local choices, perfect recall, local clock, fallback,
zero-sum payoffs and payoff bounds from the actual construction. Its theorem
bounds every NATIVE rooted-game behavioral deviation without a supplied child
Nash or regret certificate. It is not complete-plan normal-form learning.

Still required: exact runner/behavioral-policy correspondence with the original
PBS continuation, including arbitrary deviations and the extra chance fuel;
child-family/counterfactual correspondence to the parent; recursive original
paper test-time guarantee. The native theorem alone does not discharge these.
No original coverage parent is marked complete. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 remain pending. No main integration is performed.
