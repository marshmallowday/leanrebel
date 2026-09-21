# M06 reverse PBS-policy construction and coverage journal

## Source obligations and scope

The original SEARCH-CFRD row refers to main section 5.1. SEARCH-ERROR refers
to supplement appendices G and I and the cited CFR-D/DeepStack results.
SEARCH-FRONTIER refers to main sections 3 and 5.1. SAFE-THEOREM3 refers to
main section 6 and the supplement G restatement. Those original parent rows
remain pending. This journal adds a dependency slice, not an acceptance shortcut.

The inherited PBS-rooted information-set CFR had only an ORIGINAL-TO-ROOT
policy correspondence. The present implementation adds the reverse direction
for a common public cut, then transfers the native approximate Nash result
without extra loss. It does not introduce another normal-form backend.

## Construction

PBSRootLocalHistory defines AOH.rootedAt from a player's own full AOH and a
cut depth. The encoded history records an idle administrative draw, its own
root AOH snapshot, then every subsequent own action and local/public snapshot.
The map accepts no hidden root, joint action, opponent observation, realization
witness or opponent policy. pbsRootLocalHistory_read proves menu consistency
on every syntactic input. pbsRootLocalHistory_trace reconstructs every legal
rooted trace. pbsRoot_publicBelief_depth derives the common-depth premise from
the actual PublicBelief support law; it is not a solver-quality certificate.

PBSRootDecode maps arbitrary rooted behavioral policies through that local
readout. Decoding an original lift is the identity even on off-policy syntactic
original AOHs. Lifting a decoded policy agrees on every legal rooted history;
there is no assertion about arbitrary synthetic rooted AOHs. The complete
canonical rooted-history law, projected original-history law, every original
unilateral law and every history observable's expectation are preserved.

PBSInformationCFR transfers an arbitrary rooted approximate Nash profile to
the original behavioralBeliefForm, then instantiates it with the computed
fixed-positive-T information-set CFR output. Its residual is exactly the
existing pbsRootCFRBound, not zero and not an externally supplied regret bound.
Weighted infostate gaps retain the actual type mass. Unweighted conditional
behavioral gains are divided by that mass ONLY for positive-support types.

## Adversarial controls

Examples/PBSRootDecode includes the actual live factual posterior, the actual
computed CFR opponent versus a fresh randomized unilateral deviation, the
same factual conditional type slice, hidden-bit indistinguishability for ANY
decoded policy, a randomized original round trip, zero continuation fuel,
terminal roots for arbitrary new rooted profiles, and a different-cut control.
The cut control exhibits unequal encodings at distinct cut depths of the same
original AOH. Thus a decoder cannot silently assert common-cut equivalence for
arbitrary mixed-depth root laws. It is not a claim about all possible encodings.

## Original boundaries retained

The equality of laws starts from the supplied joint MODEL belief. It does not
identify that belief with an unknown opponent's true root distribution. Legal
rooted deviations are covered; a fresh unsupported root is not certified by
this on-model statement. Zero-mass conditional optimality is still not proved
by a zero-weight inequality. No numerical refinement is supplied here.

The parent counterfactual/type-conditioned value and sampled iteration family
must still be connected to the paper's independently re-solved recursive play.
Coherent redraw of one computed family is not that construction. All earlier
counterexamples, positive prediction and child errors, finite-T residuals,
and the printed/corrected Theorem 3 distinction must be retained.

## Verification state

This is a compiler checkpoint. PBSRootLocalHistory at 7ec45dc4 passed the target
compile step in run 35554030162/job 106194041761; its supplemental checks were
still running when recorded. The three downstream modules are newly registered
in the umbrella, target list and supplemental lint/axiom consumers. They are
not accepted until the new source's actual compiler and audits succeed.
The content-hashed coverage.json and all original evidence rows are unchanged.
