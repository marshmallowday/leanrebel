# M04 exact equilibrium-value checkpoint

The acceptance review located two obligations that the previous handoff did not
identify clearly. BR-ATTAINMENT is already implemented in
`GameTheory/ReBeL/FiniteSites.lean`: `exists_finitePlan_bestResponse` and
`exists_pure_bestResponse`. Its arbitrary-opponent two-stage instance and
zero-reach/no-omniscience controls are in `Examples/FiniteSites.lean`. The
characterization in `Response.lean` alone is not the evidence; the existing
finite predrawing/maximum proof is. It must be connected to coverage, not redone.

`P-EQ-VALUE-UNIQUE` is a child of M04 FOUND-NASH in the frozen paper inventory.
It is not the M05 construction/existence of a PBS equilibrium value. Accordingly,
the closing paragraph of M04-width-recovery.md must not be used to defer this
M04 child. The present module proves equality of two given exact equilibrium
values directly for the canonical GameForm and specializes it to the original
behavioral runner. It does not add a second mixed-strategy layer or claim
existence from a uniqueness theorem.

The positive regression is a nonconstant zero-sum matrix with two different
exact equilibria of value one and a dominated third row. The negative regression
removes zero sum and has two exact coordination equilibria of values one and
two. Both use the existing IsNash and unrestricted strategy replacements of
their canonical form.

The new source is a pending proof checkpoint until its own compiler, strict
axiom and normal/slow-lint results are read. The rest of the concrete CFR proof
chain remains based on f646c009e0176f703da0e434296294c17e4d8440 and the verified
net formatting repair at 108f9697e1229bd5cf60bf31bf71116dd437334d. The latter's
ReBeL run is 35371904085/job 105687607298 and full CI is
35371903881/job 105688093555; both were still running when read. M04 is not yet
accepted; original ledger obligations, M03 evidence and dependency pins remain.
