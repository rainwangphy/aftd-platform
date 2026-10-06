import AFTD.Prelude
import AFTD.Kb.Tcs.LineSyndrome

/-!
# line_syndrome_empty

Topic: quantum   Node: 2a3277205351

Provenance: helper lemma. arXiv:2610.01024, Proposition 65

The empty set has syndrome 0 under the line syndrome for n = 5.
-/

/-- Sanity lemma: the empty set has syndrome 0 under the line syndrome. -/
theorem line_syndrome_empty : line_syndrome 5 ∅ = 0 := by
  unfold line_syndrome
  decide
