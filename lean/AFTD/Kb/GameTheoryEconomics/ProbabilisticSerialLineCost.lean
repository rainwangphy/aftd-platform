import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment

/-!
# probabilistic_serial_line_cost

Topic: social_choice   Node: f9f5150bff3b

Provenance: formalization of a published result. Source: arXiv:2611.05777 (Sublinear Metric Distortion for Matching), Sec. 1 and Sec. 6: one-sided matching of n agents to n items with ordinal rankings by distance; the probabilistic serial rule (cost of a fractional matching)

The cost of the probabilistic serial assignment X for agents at a and items at b on the real line: PS = sum over agents i and items j of X_ij |a_i - b_j|.
-/

/-- Expected cost on the line of the probabilistic serial assignment: `∑ i j, X i j * |a i - b j|`. -/
noncomputable def probabilistic_serial_line_cost {n : ℕ} (a b : Fin n → ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, ∑ j, probabilistic_serial_fractional_assignment n pref i j * |a i - b j|
