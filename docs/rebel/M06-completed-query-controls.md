# Completed-query controls and exact compiler evidence

At `a1aac9c6890ed712987dccbcc83bcf6910a404d7`, targeted run `35581556267`
(job `106275374737`) compiled the full general `CFRDInformationSampling` module.
Its only failing target was the concrete examples, missing their local finite
Choice instance. This checkpoint supplies that canonical instance; no test is
removed and no inference failure is replaced by an assumption.

The next candidate `7885becccd44f16af28c8531ae83a2dea142a95d` failed the
fast line-width gate (run `35581880647`, job `106276389898`) on one 101-unit
line. This checkpoint wraps it and explicitly scopes classical decidability
inside the noncomputable query sampler. Neither changes the mathematical law.
Its new source must be recompiled; earlier source results are not acceptance.

The canonical hidden-type examples now derive a zero-factual-mass query that
has positive reference support with the actual information-set fallback.
They prove that it enters the computed-response branch and that this branch's
whole positive-fuel law equals the completed parent against an arbitrary fixed
unknown opponent. The existing factual-query, independent-versus-diagonal,
zero-fuel, and zero-model-mass controls remain. Both branch hypotheses have
actual witnesses instead of being accepted as uninhabited test assumptions.

Main and original pending M06 coverage are unchanged. The remaining original
target is noisy-parent linkage and independently re-solved recursive carried-PBS
safety, not more renaming of already completed one-PBS sampling laws.
