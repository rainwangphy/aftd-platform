import AFTD.Prelude
import AFTD.Kb.Tcs.RadialColoring
import AFTD.Kb.Tcs.RadialColoringApplyEqTrue

/-!
# radial_coloring_trivial_witnesses

Topic: combinatorics   Node: 659883e72651

Provenance: helper lemma. step towards op_1481_avoidance_three_twenty_one_exceptional_spacings

Sanity witnesses for the radial colouring: with S = Set.univ every point is coloured true, and with S = ∅ every point is coloured false. So the construction is not vacuous and both colours occur.
-/

/-- Witness that the radial colouring actually takes both values (`S = univ` is everywhere true, `S = ∅` everywhere false). -/
theorem radial_coloring_trivial_witnesses {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    radial_coloring Set.univ x = true ∧ radial_coloring (∅ : Set ℝ) x = false := by first | exact radial_coloring_apply_eq_true | (apply radial_coloring_apply_eq_true <;> assumption) | (apply radial_coloring_apply_eq_true <;> simp_all) | simpa using radial_coloring_apply_eq_true | (simp only [radial_coloring] at *; first | exact radial_coloring_apply_eq_true | (apply radial_coloring_apply_eq_true <;> assumption) | (apply radial_coloring_apply_eq_true <;> simp_all) | simpa using radial_coloring_apply_eq_true)
