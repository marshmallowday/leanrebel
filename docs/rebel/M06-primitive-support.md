# Primitive good-state support rates

Project dependency for ROADMAP M06, not paper Theorem 3. The parent is
03d75bf7638ee06073840ae95475dafbc77da47b, the target-acceptance descendant of
latest starting checkpoint 2a7c55aabd3e5d352bfac7d132d3582879d738e1.
Implementation branch: `rebel/m06-primitive-support-20260927`.

## Statements and assumptions

The existing generic FinDistFirstHit module gains firstHitRateBudget,
firstHitRateBudget_nonneg and sequenceFirstHitProbability_le_rateBudget.
For a fixed bad set B, stage events E[k] contained in B, and nonnegative
rates r[k], assume P(next in B | state) <= r[k] only at states outside B.
Then the existing native first-hit probability is at most
mu[0](B) + sum over k < schedule.length - 1 of r[k]. Empty and singleton
schedules have no transition budget. Empty schedules still have actual hit
probability zero; the bound conservatively retains the initial bad mass.

This is proved by first-hit induction, not the expected number of visits.
After a bad state is reached, arbitrary persistence or recovery is allowed.
No smallness premise is imposed at bad states. The last transition is excluded:
its output is not an input to another scheduled stage. Stage events can be a
strict subset of B, so missing or stopped beliefs can be conservatively charged
without being incorrectly called live sampling exceptions. The bound is not a
visit-count theorem and is not a changed native probability law.

PBSCarriedSupport gains executionSupportCharge_le_mul: the actual one-step
missing-model-support rate bounds the fuel-step charge by fuel * rate.
carriedResolvedSupportCharge_le_of_step_leakage applies this only at supported
incoming states and only to profiles actually sampled by the native resolver.
carriedMemorySequence_firstHit_le_primitiveRate composes these facts under
arbitrary actual full-state laws, and
pbsCarriedDepthFirstHitProbability_le_primitiveRate discharges event containment
for the existing noisy depth-limited CFR factory. Both use the probability cap 1.
The unknown opponent is fixed throughout; each private chosen profile remains
paired with its own stored joint PBS and carried memory. No marginal-product
reconstruction or actual/model posterior equality is assumed.

Primitive nonnegative rates and their one-step leakage inequalities are
EXPLICIT PREMISES. This does not prove those rates are small for unrestricted
finite-T CFR, and does not turn child equilibrium quality into a support bound.
Source-specific smallness and the signed native/late value/security bounds
remain separate M06 obligations. No learner-convergence premise is introduced.

## Adversarial controls and trust

The added stickyQuarterLeak example has bad-state leakage 1 but good-state
leakage 1/4. Five named Lean controls prove the good bound, bad-state unit
probability, the three-input rate allowance 1/2, exact first-hit probability
7/16, and singleton zero transition budget. Its three-input visit mass is
11/16 (independent Fraction fixture), strictly larger than the new 1/2 bound;
this rejects misusing the theorem for visit counts.

Seven new Fraction tests include absorbing failures, recovery, final-output
exclusion, empty/singleton cases, private-model pairing and rejected premises.
Independent full path enumeration checks 2,187 inhomogeneous three-stage cases.
All 134 fixtures, plus ledger/inventory structure checks, passed locally on
the 4784 snapshot with the two changed Lean blobs and this test file. This is
not local Lean compilation or verification of the final remote documentation.

All prior source and controls are preserved. Both edited modules already occur
in the declared M06 targets, explicit target lint/axiom consumer, and global
import closure. No module is hidden and no dependency, workflow, allowlist,
architecture budget or expected count is relaxed. Exact-source compiler,
normal/slow lint and complete transitive-axiom inspection are pending for these
new proofs; older target acceptance does not validate them.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 is incomplete. Record actual target/global/full-CI identities after push
and repair any failure without changing the statements. No background work
is promised.
