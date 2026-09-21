# M06 sampling: semantic review and coverage journal

Proof source: 72a837daf5f5e295b38e3da67765b3f7f4278425.
Compiler/lint/axiom acceptance is recorded separately in
M06-information-sampling-validation.md. This review does not replace it.

## What the constructions establish

1. PBSInformationSampling.pbsRootCFRIterate instantiates the existing
   cfrPlay recurrence. The new draw is uniform over the actual completed
   iterations, not an arbitrary family, independently chosen equilibrium,
   deterministic-plan approximation or last-iterate replacement.
2. pbsInformationCFR_sampling_law and delayed_sampling preserve complete
   original histories against any fixed behavioral opponent. That opponent
   can react to its information but is not given the private iteration index.
   The index is sampled once for this continuation and retained throughout it.
3. cfrDInformationChildProfile_sampling connects the same draw to the
   existing factual child table and public-prefix-spliced child profile,
   using precisely the existing posterior-dependent positive child count.
4. pbsInformationCFR_sampling_from_support does not infer pointwise equality
   merely from equality of averages. It proves that complete histories keep
   disjoint prefixes at the common public cut, isolates one fiber, and cancels
   only a strictly nonzero root probability.
5. pbsInformationCFR_sampling_reweighted and its value theorem permit any
   root distribution whose support is included in that model belief. This
   includes conditioning or changed probabilities, not newly introduced roots.
   The zero-mass counterexample rejects unsupported cancellation explicitly.

## Relationship to original coverage parents

SEARCH-CFRD: advances the actual child iteration family, own-reach average
and private delayed draw. Independent recursive child solving with carried
parent memory and the complete paper algorithm correspondence remain pending.

SEARCH-FRONTIER: preserves the original public cut and proves a prefix readout
used only in the proof. No hidden root or complete history is added to any
policy's input. This is not a new acceptance of the whole frontier/search path.

SEARCH-ERROR: the proved law substitutions themselves add no error to the
observables they preserve. This does not remove prediction error, finite-T
regret, positive child tolerance or losses from a different recursive solver.

SAFE-THEOREM3: supported conditional laws are a new dependency. They do not
supply the unknown opponent's actual posterior, support inclusion at every
recursive stage, omitted-type completion or independent re-solving safety.
The printed/corrected theorem distinction and all inherited counterexamples
remain necessary. The content-hashed coverage parents are therefore NOT closed.

## Next dependency, without circular certificates

Connect these actual sampled iterates to cfrDInformationContinuation, whose
cfrDCompleteZeroReach and cfrDPublicResponseCompletion handle omitted own types.
Prove the required conditional reference-law and value correspondences for
that completed iteration family instead of assuming them as a certificate.
Then construct the recursive carried-PBS state and establish its execution
correspondence inductively for independently solved children. Fixed-family
redraw, arbitrary Nash reselection and per-action resampling are not substitutes.

Twelve theorem controls cover the live canonical hidden-type setup, positive
and zero fuel, randomized opponents, the actual parent splice, supported root
conditioning, values and the generic zero-mass failure. These are Lean theorem
fixtures, not a numerical runtime benchmark of the real-valued child solver.
