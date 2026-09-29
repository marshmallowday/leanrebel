# Rooted-child recursive consumers: 3246e17 failure and proof repair

Candidate: 3246e17090f3c363b79ef8bc3b74e12b2cb6d857.
Accepted baseline remains c1edc995d1a9790ae569c3edbdd23c2a7e99199b.
All four workflows completed at this exact SHA before the repair.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36520126583](https://github.com/marshmallowday/leanrebel/actions/runs/36520126583) | 109250935502 | failure |
| ReBeL checks | [36520126486](https://github.com/marshmallowday/leanrebel/actions/runs/36520126486) | 109250935341 | failure |
| Targeted | [36520126559](https://github.com/marshmallowday/leanrebel/actions/runs/36520126559) | 109250935910 | failure |
| Inventory | [36520126534](https://github.com/marshmallowday/leanrebel/actions/runs/36520126534) | 109250935719 | success |

Source snapshot job 109250935574 succeeded. Complete decoded logs were read.
The previous dependent endpoint repair compiled: PBSRootChildDecode succeeded
in CI/checks/target in 4.2/3.6/3.7 seconds. This does not validate its full lint
or axiom closure. The three compiler jobs now have the same two diagnostics
in PBSRootChildRecursive; all three contain zero axiom records.
The recursive module, examples, umbrella, full build/lint/axioms are not accepted.

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 245 Python tests in 9.671 seconds.
Inventory passed 245 tests in 10.117 seconds.

## Complete common diagnostics

```text
error: GameTheory/Analysis/ReBeL/PBSRootChildRecursive.lean:84:48: unsolved goals
E : ExecutionProtocol (Fin 2)
M : InformationModel E
outerObs : List M.PublicSignal
outer : PublicBelief (fullInformation M).toInfoSignals outerObs
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
noise : PBSRecursiveDepthNoise
cuts : List ℕ
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
bound : ℝ
trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature
cut : ℕ
loss : ℝ
observations : List M.PublicSignal
past : List (Option (List M.PublicSignal))
possible :
  CFRDFactualChildPossible (pbsRootInformation (fullInformation M) outer.law) trunk cut cuts.sum
    (some observations :: past)
child : PublicBelief (fullInformation (pbsRootInformation (fullInformation M) outer.law)).toInfoSignals
  (some observations :: past) :=
  cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut cuts.sum
    (some observations :: past) possible
⊢ pbsRootDecodeProfile M outer.law (outerObs.length - 1)
      (pbsRecursiveDepth noise cuts (pbsRootProtocol outer.law) (pbsRootInformation (fullInformation M) outer.law)
        (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff) bound
        (cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut cuts.sum
          (some observations :: past) possible)
        ((cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut cuts.sum
                (some observations :: past) possible).law.positiveMassFloor *
          loss)) =
    pbsRootDecodeProfile M outer.law (outerObs.length - 1)
      (pbsRecursiveDepth noise cuts (pbsRootProtocol outer.law) (pbsRootInformation (fullInformation M) outer.law)
        (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff) bound child
        (child.law.positiveMassFloor * loss))
error: GameTheory/Analysis/ReBeL/PBSRootChildRecursive.lean:257:2: Type mismatch
  estimate
has type
  |(decoded.law.bind ((fullInformation M).runBehavioralFrom internal freshCuts.sum)).expect (payoff who) -
        (decoded.law.bind ((fullInformation M).runBehavioralFrom fresh freshCuts.sum)).expect (payoff who)| ≤
    internalError + freshError
but is expected to have type
  |(decoded.law.bind ((fullInformation M).runBehavioralFrom internal internalCuts.sum)).expect (payoff who) -
        (decoded.law.bind ((fullInformation M).runBehavioralFrom fresh freshCuts.sum)).expect (payoff who)| ≤
    internalError + freshError
```

## Repair and commit-before type review

Both problems are repaired together, with no definition or theorem signature
change. In pbsRootChildRecursive_selected, restricted simp exposes the actual
selected call but leaves the local definition child on one side. Add rfl to
close the displayed definitional equality, including the identical
child.law.positiveMassFloor * loss request. No posterior or policy equality is
assumed.

In pbsRootChildRecursive_fresh_value, the existing rewrite turns both execution
fuels in estimate into freshCuts.sum, but the goal still uses internalCuts.sum
on its first execution. Rewrite the goal with the same horizon equality before
exact estimate. The two solver profiles remain the distinct local definitions;
their cut lists, noise, fallback and requested errors are not equated. This uses
the already explicit same-total-horizon premise, in its stated forward direction.

The previous static review missed both the open definitional equality after
simp only and the one-sided fuel normalization. Comparing the actual goal types
now makes those failures explicit. Removing the two added tactic lines restores
the parent Lean file byte for byte. All definitions, theorem statements,
instances, remaining proofs, concrete examples, tests, workflows, audit criteria,
heartbeat limits and source pins are unchanged.

Re-read the actual PBSChildSolve and cfrDComposedChildTable definitions,
cfrDComposedChildProfile_beliefLaw, pbsRecursiveDepth_isNash and
pbsRecursiveDepthDraw_law signatures, behavioralNash_crossRoot_value_abs_le and
the accepted same-horizon crossQuery consumer. Re-read the complete decoder,
all selected/parent-law/Nash/draw/security/fresh-value consumers and all five
rooted hidden-type examples. The fullInformation six universes, rooted/original
History/Choice/InfoState carriers, public Option-list index and dependent child
law are unchanged. The proof-local child is exactly the factual child selected
by the same possible witness. Table requests still use positiveMassFloor * loss.

The first Nash proof has internalCuts.sum; freshNash is rewritten backward to
that fuel before applying the scalar helper; both estimate and goal are then
normalized forward to freshCuts.sum. Both tolerances remain independent. The
actual parent cut is 2, the child remaining horizon is 1, and fresh cuts [1]
have sum 1 in the concrete integration. The outer AOH decoding cut is separate.
Private-law and public-splice consumers retain arbitrary later fuel, zero
continuation retains the child law, and no administrative root draw is repeated.
Typed PBSChildSolve and trunk profiles, history and choice instances, fixed
unknown opponent, draw retention and payoff directions were checked throughout.

This is static review, not local Lean compilation or audit/test execution.
Core lines remain at most 100 characters. The expected surface remains 199 build
targets, 161 targeted/301 global audit modules and 245 Python tests. Same-new-SHA
Actions must validate both fixes and the previously unreached examples/lint.

## Artifact metadata

ZIP contents were not read. Complete decoded logs are the diagnostic evidence.
Metadata:
- Target 11012926426, 5381 bytes,
  sha256 9c8d8a6ac24dc8763610ebc421480bdbcb96f138f6f68107728f0b6592c9b08f.
- Global 11013486997, 21826 bytes,
  sha256 9959e921ea69ece32a457a280158c10dab5c6dd1c777fef318853bbdedd340e0.
- Source 11013065027, 3045450 bytes,
  sha256 e25b51129018be0409410e5b29486444ac2b7e9d81ab05a5075b10dc010bf65e.
- CI and inventory: no artifacts.

M06 remains incomplete. MODEL-law decoding and same-horizon scalar comparison
do not prove native successive-query calibration, policy/algorithm identity
or full recursive small-rate safety. Remaining paper obligations stay pending.
