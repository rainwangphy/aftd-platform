import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoTypeChoresHaveAlphaPmmsFpo
import AFTD.Kb.GameTheoryEconomics.IsAlphaPmmsTwoTypeChores
import AFTD.Kb.GameTheoryEconomics.IsTwoTypeAllocation
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimalTwoTypeChores

/-!
# op886_two_type_chores_alpha_pmms_fpo_mono

Topic: fair_division   Node: ed1486862239

Provenance: helper lemma. OP-886

For real numbers alpha ≤ beta, if the universal existence property two_type_chores_have_alpha_pmms_fpo alpha holds, then two_type_chores_have_alpha_pmms_fpo beta also holds.
-/

/-- Monotonicity of the universal alpha-PMMS fractional Pareto optimal allocation property. -/
theorem op886_two_type_chores_alpha_pmms_fpo_mono {α β : ℝ} (hαβ : α ≤ β)
    (h : two_type_chores_have_alpha_pmms_fpo α) :
    two_type_chores_have_alpha_pmms_fpo β := by
  intro n hn a b p q hp hq
  rcases h n hn a b p q hp hq with ⟨x, y, halloc, hfpo, hpmms⟩
  refine ⟨x, y, halloc, hfpo, ?_⟩
  intro i j hij s t hs ht
  have h_le := hpmms i j hij s t hs ht
  have h_nonneg : 0 ≤ max (p i * (s : ℝ) + q i * (t : ℝ))
      (p i * ((x i + x j - s : ℕ) : ℝ) + q i * ((y i + y j - t : ℕ) : ℝ)) := by
    have h1 : 0 ≤ p i * (s : ℝ) := mul_nonneg (hp i).le (Nat.cast_nonneg s)
    have h2 : 0 ≤ q i * (t : ℝ) := mul_nonneg (hq i).le (Nat.cast_nonneg t)
    have h3 : 0 ≤ p i * (s : ℝ) + q i * (t : ℝ) := add_nonneg h1 h2
    exact le_trans h3 (le_max_left _ _)
  exact le_trans h_le (mul_le_mul_of_nonneg_right hαβ h_nonneg)
