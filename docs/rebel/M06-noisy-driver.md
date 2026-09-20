# M06 bounded numerical predictions on the constructed child solver

Parent: 3ec0f0b4dc77ef1524bd4165bba22082ab772b22, whose target compiler step
passed. This new checkpoint requires independent exact-SHA validation.

CFRDNoisyDriver constructs a response using exact child Nash and off-path
completion at the CURRENT queried trunk, then adds an information-local
prediction error. The oracle drives the real coupled cfrDState recurrence.
The proof does not reuse the exact driver's learning sequence: numerical
perturbations can change every future query and trunk. At every such new
query, child optimality is constructed again, independently of prediction noise.

A uniform absolute numerical error bound derives CFRDDepthAccurate for the
perturbed sequence. CFRDDepthLeafOptimal at zero child loss needs no numerical
bound. Instantiating the carried-execution theorem yields A*error+B/sqrt(T),
with the explicit existing game/depth/payoff constants. The finite-T term
remains when error is zero. The comparison Nash profile names the original
game value, not a child equilibrium supplied to the constructor.

Three new live HiddenTypes controls instantiate error 1/4, derived leaf
optimality and prediction difference 1/4 at the same query. They do not assert
that a constant bias must change the learned policy. All previous six new
exact-driver controls and every inherited negative test remain compiled targets.

Scope: exact noncomputable children, finite-T outer CFR-D, bounded numerical
predictions, and a private iteration retained across the cut. This is not a
proof of finite-T approximate child solves, arbitrary re-solving, network
accuracy, or the printed Theorem 3 formula. Original coverage parents remain
pending until the remaining construction and semantic acceptance review.
