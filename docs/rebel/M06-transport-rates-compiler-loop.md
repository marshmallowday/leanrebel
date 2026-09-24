# M06 transport rates: exact-source compiler loop

The task branch is rebel/m06-transport-rates-20260924; main and predecessor
proof/review refs are not modified. Every source write is through the GitHub
plugin. Local execution became unavailable with tool ClientError responses;
there is no claimed local Lean or lint pass for this new slice.

## Checkpoints and failed gates

- 53e99a3bc48ced27efdc3beb0f307e32c0a1d37c: restart/plan after predecessor review
  1c509f60f823505a36318e54735f61e00dd49aab.
- cc4bf7aecb83f75929f568bf0dd4950578d4cafa: initial FinDistTransportRate draft.
  ReBeL run35990359854/job107603115729 failed static TRANSPORT_MATH_SOURCE:
  expected1, observed3. The parameter identifier `change` was counted twice as
  the tactic keyword. Library width passed. The guard was not weakened.
- d8ecb881dcfe8553e885ffccc240645249221072: root, target and supplemental-audit
  registration, preserving all128 inherited targets and90 inherited audit
  modules. The same static identifier collision remained in this checkpoint.
- 3687ea396aabc27392120858dfa0d251db33e833: rename the density premise to
  `hdensity`. Target run35991664528/job107606957908 then exposed actual Lean
  errors: statement-level decidability for two fiber formulas, an insufficiently
  explicit fiber sum and a ring normalization attempted outside absolute values.
  All128 inherited targets compiled; the new math module failed. Supplemental
  lint/axiom audit was skipped, not passed. Artifact10804516662 contains the
  exact log; ZIP SHA256 is
  1a41042ad25fa446e5f0dd592dff7c02860aebee98c7b08ddc7941b94e199d49.
- 79f3a876a14e58f6e9f9f06f602457be82fbe4d6: add explicit DecidableEq only to the
  two indicator-formula interfaces, unfold the fiber sum and normalize the
  scalar identity before applying the absolute-value triangle inequality.

## Game-consumer and adversarial-control checkpoint

The next commit adds CFRDSourceRates and Examples.CFRDSourceRates, plus both
modules to the analytic root, all-target build and unchanged transitive auditor.
Counts become131 M06 targets and93 supplemental modules. No existing entry,
proof, workflow, toolchain pin or allowed-axiom restriction is removed.

CFRDSourceRates expresses the old positive conditional value change through
actual continuation outcome-law L1 discrepancies and expresses conditional
transport through unnormalized reference atoms with the exact unknown-opponent
density. The expectation remains over the actual private seed/history law.
The canonical security consumer keeps parent bias1/8, old child loss1/4,
finite parent time and two newly computed finite child solves.

The finite tests use two joint Bool-by-Bool source laws, one common observation,
rare observation mass1/100 and a changed hidden atom on that fiber. They test
normalization through public probabilities, OLD weighted defect1/50 versus
actual concentrated defect2, necessity of the density, NEW-only source atoms,
disappearing NEW queries and absent OLD queries. These are formal controls,
not claimed counterexamples to source Theorem3.

At this checkpoint all new game/control declarations remain UNVERIFIED pending
exact-source compiler, normal/slow lint and public/private/generated axiom audit.
No M06 parent coverage status is promoted. In particular, a source-discrepancy
bound is not yet a vanishing algorithm-native rate without proving its inputs
small; later carried-PBS independent re-solving and native first-exit rates
remain open proof obligations in this repository.
