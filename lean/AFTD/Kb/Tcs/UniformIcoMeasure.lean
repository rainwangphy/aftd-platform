import AFTD.Prelude

/-!
# uniform_Ico_measure

Topic: online_algorithms   Node: 643e83948735

Provenance: formalization of a published result. Source: Mathlib.MeasureTheory.Measure.MeasureSpaceDef

The uniform probability measure on the half-open interval [a, b), defined as normalized Lebesgue measure restricted to [a, b).
-/

/-- Uniform probability measure on the interval [a, b). -/
noncomputable def uniform_Ico_measure (a b : ℝ) : MeasureTheory.Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • MeasureTheory.volume.restrict (Set.Ico a b)
