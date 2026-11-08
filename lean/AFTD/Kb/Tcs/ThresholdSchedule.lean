import AFTD.Prelude
import AFTD.Kb.Tcs.ThresholdState

/-!
# threshold_schedule

Topic: online_algorithms   Node: ce203e26a8c6

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 5

Given horizon T : ℕ, increments a : Fin (T - 1) → NNReal, reset price K : ℝ, and call t : Fin T, threshold_schedule T a K t : Bool is decide (K ≤ (acc : ℝ) + (h : ℝ)) where (h, acc) = threshold_state T a K t.
-/

/-- The schedule produced by the threshold rule on a session with horizon T, increments a, and reset price K. -/
noncomputable def threshold_schedule (T : ℕ) (a : Fin (T - 1) → NNReal) (K : ℝ) (t : Fin T) : Bool := let (h, acc) := threshold_state T a K t
  decide (K ≤ (acc : ℝ) + (h : ℝ))
