import AFTD.Prelude
import AFTD.Kb.Tcs.CubicHypergraphMeasure
import AFTD.Kb.Tcs.CubicEdge
import AFTD.Kb.Tcs.CubicHypergraph

/-!
# instIsProbabilityMeasureCubicHypergraphMeasure

Topic: quantum   Node: 5bc0d4602e3d

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For every natural number n, cubicHypergraphMeasure n is a probability measure in the sense of MeasureTheory.IsProbabilityMeasure.
-/

/-- Probability measure instance for cubicHypergraphMeasure. -/
instance instIsProbabilityMeasureCubicHypergraphMeasure (n : ℕ) : MeasureTheory.IsProbabilityMeasure (cubicHypergraphMeasure n) := by dsimp [cubicHypergraphMeasure]; infer_instance
