import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcxPoly

/-!
# pcx_poly_three_roots

Topic: equilibria   Node: 0128649d8a2f

pcx_poly has a root in each of (11/100, 12/100), (26/100, 27/100) and (41/100, 42/100).
-/

/-- `pcx_poly` has a root in each of the open intervals `(11/100, 12/100)`, `(26/100, 27/100)` and `(41/100, 42/100)`. -/
lemma pcx_poly_three_roots :
    ∃ x₁ x₂ x₃ : ℝ, 11 / 100 < x₁ ∧ x₁ < 12 / 100 ∧ 26 / 100 < x₂ ∧ x₂ < 27 / 100 ∧
      41 / 100 < x₃ ∧ x₃ < 42 / 100 ∧ pcx_poly x₁ = 0 ∧ pcx_poly x₂ = 0 ∧ pcx_poly x₃ = 0 := by
  have hc : Continuous pcx_poly := by unfold pcx_poly; fun_prop
  obtain ⟨x₁, ⟨a1, b1⟩, e1⟩ := intermediate_value_Ioo (show (11 / 100 : ℝ) ≤ 12 / 100 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcx_poly (11 / 100)) (pcx_poly (12 / 100)) by
      constructor <;> norm_num [pcx_poly])
  obtain ⟨x₂, ⟨a2, b2⟩, e2⟩ := intermediate_value_Ioo' (show (26 / 100 : ℝ) ≤ 27 / 100 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcx_poly (27 / 100)) (pcx_poly (26 / 100)) by
      constructor <;> norm_num [pcx_poly])
  obtain ⟨x₃, ⟨a3, b3⟩, e3⟩ := intermediate_value_Ioo (show (41 / 100 : ℝ) ≤ 42 / 100 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcx_poly (41 / 100)) (pcx_poly (42 / 100)) by
      constructor <;> norm_num [pcx_poly])
  exact ⟨x₁, x₂, x₃, a1, b1, a2, b2, a3, b3, e1, e2, e3⟩
