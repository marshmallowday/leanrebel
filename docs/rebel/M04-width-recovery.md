# M04 width-gate recovery

The source `f646c009e0176f703da0e434296294c17e4d8440` passed the complete
ReBeL checks (run 35363536383/job 105660357662), but the full-library workflow
35363536384/job 105660678715 failed after its successful 4089-job build at
Phase 3: `LIBRARY_LINES_OVER_100: expected 0, got 7`; maximum width 136.
The earlier run identifier 35363536494 was a transcription error, not an
access denial. The correct source artifact is 10554754280.

Recovery anchor `609d111a4b247a04bd75f2598c5baeadbdb91133` records the actual
state in STATUS and adds an early, unchanged-width diagnostic. Its run
35371274354/job 105685560599 reported exactly the same seven violations:

- Examples/RationalAverage: two declaration lines, widths 101/101.
- Examples/RationalCounterfactual: one declaration line, width 103.
- Examples/RationalIteration: one declaration line, width 106.
- RationalAverage: one declaration line, width 101.
- ReBeL/Rational/HiddenTypes: two CSV rendering lines, widths 107/136.

The present source change only wraps those declarations and splits the two
CSV strings by concatenation without inserting output characters. It does not
alter proof statements, solver updates, averaging, deviations, test cases,
dependency pins, architecture expectations, or axiom policy. Its own target-SHA
build, runtime comparison, lint and all full-library gates still need checking.

Do not promote coverage or integrate main until those checks and the M04
semantic acceptance review are complete. The unfinished loose value-uniqueness
blob from the prior session is not a committed M04 result; the ROADMAP assigns
PBS value/existence/minimax work to M05, and no theorem is accepted from a blob.
