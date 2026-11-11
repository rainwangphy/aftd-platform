import AFTD.Prelude

/-!
# balanced_draft_uniform_unit_law

Topic: fair_division   Node: 62dbe59009b4

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The probability measure obtained by restricting Lebesgue measure to the closed unit interval.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_uniform_unit_law : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Icc 0 1), ⟨by simp [Measure.restrict_apply, Real.volume_Icc]⟩⟩
