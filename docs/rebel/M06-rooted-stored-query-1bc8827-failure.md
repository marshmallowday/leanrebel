# Rooted saved-query candidate 1bc8827: rewrite below local lets

Candidate: 1bc8827dae4f5ba7f1903abf172536e155bf5a14.
Accepted baseline remains 3f09be2d2b6bbb5e222e6b189f5bc409362ad148.
M06 and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain incomplete.

## Exact-SHA evidence

- CI [36529480526](https://github.com/marshmallowday/leanrebel/actions/runs/36529480526), job109279686667: failure.
- ReBeL checks [36529480546](https://github.com/marshmallowday/leanrebel/actions/runs/36529480546), compiler job109279686864: failure; source job109279686674: success.
- Targeted [36529480522](https://github.com/marshmallowday/leanrebel/actions/runs/36529480522), job109279686148: failure.
- Inventory [36529480587](https://github.com/marshmallowday/leanrebel/actions/runs/36529480587), job109279686455: success.

All five complete decoded job logs were read. The three compiler jobs report
the same sole source diagnostic at PBSRootStoredValue.lean:140:6, including
identical complete contexts. Each has zero axiom records. Full build, downstream
saved-state/examples, complete lint and axioms are NOT accepted. Checks passed
LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0, RATIONAL_RUNTIME_PASS,
and250 Python tests in9.851s. Inventory passed250 tests in10.780s.

Artifact metadata was inspected; ZIP contents were not read:

- m06-targeted-1bc8827dae4f5ba7f1903abf172536e155bf5a14: id11015887872, 5695bytes, sha256:bd105fbb1853c97c1ba7c92848717ef100532a7ab0fc79a703ee829c525bba8b.
- rebel-source-1bc8827dae4f5ba7f1903abf172536e155bf5a14: id11016340721, 3090010bytes, sha256:0e2c963b3974bf0b6ec5f34b516f121f078db67b8ca531731d6d97d46bbcde9b.
- rebel-validation-1bc8827dae4f5ba7f1903abf172536e155bf5a14: id11015659423, 21983bytes, sha256:33dca66e6b79bc7eaee6a7d9018395e59ee2d180504f5d3f2fcd8982b6ac329f.

CI and inventory have no artifacts. Complete decoded logs, not ZIP contents,
are the compiler evidence. Older successful source is not reused as acceptance.

## Repair and commit-before type review

The common-kernel error theorem returns two local let binders in its type.
`rw [abs_sub_comm] at error` did not descend through them. Insert
`dsimp only at error` immediately before that rewrite, then retain `exact error`.
The one added line is the entire Lean change; removing it reproduces the parent
file byte for byte. Definitions, theorem signatures, assumptions, instances,
other proofs, examples, tests, workflow/audit criteria and heartbeat limits stay
unchanged. No linter or proof requirement is disabled.

Re-read pbsRootDecoded_public_error, behavioralNash_crossRoot_value_abs_le,
pbsRecursiveDepth_private_model_security, cfrDComposedRound_storedPublic and
FinDist.condOn_eq_of_support_iff with all new value/state/example consumers.
Both local posteriors are the same indexed values already introduced in the
consumer. Zeta reduction exposes the absolute subtraction; its public-minus-live
direction is reversed to the required live-minus-public direction. Original
fullInformation six universes, rooted signal carrier, independent Outcome/K,
state.history-dependent PBS and Option law projection remain unchanged.
Both Nash fuels and fresh private fuel use remaining; private security retains
internalError+2*freshError and the stopped fraction. Downstream gap/security
already reduce their lets before rewriting; saved-law composition uses ordinary
definitional equality and support-equivalent events, not a dependent PBS cast.
All four examples retain actual typed child solve/trunk, cut2/remaining1,
mass-scaled child request, fixed unknown and retained private draw. No other
analogous absolute-subtraction rewrite under unexpanded lets was found in this
batch. Core maximum line length99; no forbidden transport pattern introduced.

The previous static review missed the let wrappers visible in the actual
compiler context. This repair is still static, not a successful Lean compile.
All same-SHA Actions gates remain required. Semantic scope and outstanding
native calibration, changing-clock and small-rate obligations are unchanged.

## Complete common compiler diagnostic

```text
error: GameTheory/Analysis/ReBeL/PBSRootStoredValue.lean:140:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  |?a - ?b|
in the target expression
  have posterior := pbsRootPublicPosterior M outer.law trunk cut remaining observations past possible;
  have child :=
    cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut remaining
      (some observations :: past) possible;
  |((pbsRootChildBelief M outer.law posterior).law.bind
              ((fullInformation M).runBehavioralFrom profile remaining)).expect
          (payoff who) -
        ((pbsRootChildBelief M outer.law child).law.bind
              ((fullInformation M).runBehavioralFrom profile remaining)).expect
          (payoff who)| ≤
    2 * bound * pbsRootStoppedFraction M outer.law trunk cut remaining observations past

E : ExecutionProtocol (Fin 2)
M : InformationModel E
outerObs : List M.PublicSignal
outer : PublicBelief (fullInformation M).toInfoSignals outerObs
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature
cut remaining : ℕ
observations : List M.PublicSignal
past : List (Option (List M.PublicSignal))
possible :
  CFRDFactualChildPossible (pbsRootInformation (fullInformation M) outer.law) trunk cut remaining
    (some observations :: past)
internalNoise freshNoise : PBSRecursiveDepthNoise
internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise
freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise
internalCuts freshCuts : List ℕ
internalHorizon : internalCuts.sum = remaining
freshHorizon : freshCuts.sum = remaining
internalFallback freshFallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
zeroSum : IsZeroSum fun h who ↦ payoff who h
bound : ℝ
nonneg : 0 ≤ bound
bounded : ∀ (who : Fin 2) (h : E.History), |payoff who h| ≤ bound
internalError freshError : ℝ
internalPositive : 0 < internalError
freshPositive : 0 < freshError
who : Fin 2
posterior : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals (some observations :: past) :=
  pbsRootPublicPosterior M outer.law trunk cut remaining observations past possible
child : PublicBelief (fullInformation (pbsRootInformation (fullInformation M) outer.law)).toInfoSignals
  (some observations :: past) :=
  cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut remaining
    (some observations :: past) possible
decodedPublic : PublicBelief (fullInformation M).toInfoSignals observations := pbsRootChildBelief M outer.law posterior
decodedChild : PublicBelief (fullInformation M).toInfoSignals observations := pbsRootChildBelief M outer.law child
internal : Profile (fullInformation M).behavioralSignature :=
  pbsRootChildRecursiveProfile M outer internalNoise internalCuts internalFallback payoff bound child internalError
fresh : Profile (fullInformation M).behavioralSignature :=
  pbsRecursiveDepth freshNoise freshCuts E M freshFallback payoff bound decodedPublic freshError
internalNash :
  IsNash (behavioralBeliefForm (fullInformation M) (pbsRootChildBelief M outer.law child) remaining)
    (euPreferenceWithin internalError fun h who ↦ payoff who h)
    (pbsRootChildRecursiveProfile M outer internalNoise internalCuts internalFallback payoff bound child internalError)
freshNash :
  IsNash (behavioralBeliefForm (fullInformation M) decodedPublic remaining)
    (euPreferenceWithin freshError fun h who ↦ payoff who h)
    (pbsRecursiveDepth freshNoise freshCuts E M freshFallback payoff bound decodedPublic freshError)
profile : Profile (fullInformation M).behavioralSignature
error :
  have posterior := pbsRootPublicPosterior M outer.law trunk cut remaining observations past possible;
  have child :=
    cfrDFactualChildBelief (pbsRootInformation (fullInformation M) outer.law) trunk cut remaining
      (some observations :: past) possible;
  |((pbsRootChildBelief M outer.law posterior).law.bind
              ((fullInformation M).runBehavioralFrom profile remaining)).expect
          (payoff who) -
        ((pbsRootChildBelief M outer.law child).law.bind
              ((fullInformation M).runBehavioralFrom profile remaining)).expect
          (payoff who)| ≤
    2 * bound * pbsRootStoppedFraction M outer.law trunk cut remaining observations past
⊢ |(decodedChild.law.bind ((fullInformation M).runBehavioralFrom profile remaining)).expect (payoff who) -
        (decodedPublic.law.bind ((fullInformation M).runBehavioralFrom profile remaining)).expect (payoff who)| ≤
    2 * bound * pbsRootStoppedFraction M outer.law trunk cut remaining observations past
```
