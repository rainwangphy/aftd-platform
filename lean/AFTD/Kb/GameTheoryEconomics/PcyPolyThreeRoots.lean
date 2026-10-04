import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcyPoly

/-!
# pcy_poly_three_roots

Topic: equilibria   Node: 93496ba25793

pcy_poly has a root in each of (2, 21/10), (12/5, 5/2) and (29/10, 3).
-/

/-- `pcy_poly` has a root in each of the open intervals `(2, 21/10)`, `(12/5, 5/2)` and `(29/10, 3)`. -/
lemma pcy_poly_three_roots :
    ∃ y₁ y₂ y₃ : ℝ, 2 < y₁ ∧ y₁ < 21 / 10 ∧ 12 / 5 < y₂ ∧ y₂ < 5 / 2 ∧ 29 / 10 < y₃ ∧ y₃ < 3 ∧
      pcy_poly y₁ = 0 ∧ pcy_poly y₂ = 0 ∧ pcy_poly y₃ = 0 := by
  have hc : Continuous pcy_poly := by unfold pcy_poly; fun_prop
  obtain ⟨y₁, ⟨a1, b1⟩, e1⟩ := intermediate_value_Ioo' (show (2 : ℝ) ≤ 21 / 10 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcy_poly (21 / 10)) (pcy_poly 2) by
      constructor <;> norm_num [pcy_poly])
  obtain ⟨y₂, ⟨a2, b2⟩, e2⟩ := intermediate_value_Ioo (show (12 / 5 : ℝ) ≤ 5 / 2 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcy_poly (12 / 5)) (pcy_poly (5 / 2)) by
      constructor <;> norm_num [pcy_poly])
  obtain ⟨y₃, ⟨a3, b3⟩, e3⟩ := intermediate_value_Ioo' (show (29 / 10 : ℝ) ≤ 3 by norm_num)
    hc.continuousOn (show (0 : ℝ) ∈ Set.Ioo (pcy_poly 3) (pcy_poly (29 / 10)) by
      constructor <;> norm_num [pcy_poly])
  exact ⟨y₁, y₂, y₃, a1, b1, a2, b2, a3, b3, e1, e2, e3⟩
