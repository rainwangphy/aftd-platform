import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformationSubadditive
import AFTD.Kb.Tcs.MutualFInformationAdd
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.MutualFInformationConstMul

/-!
# mutual_f_information_subadditive_add_mul

Topic: information   Node: 9e3ba73f61fc

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. II, the remark after Corollary 1 (nonnegative combinations of subadditive generators are subadditive).

If f₁ and f₂ are subadditive generators for mutual f-information (mutual_f_information_subadditive, i.e. Ĩ_f(X; YZ) ≤ Ĩ_f(X; Y) + Ĩ_f(X; Z) for all finite Markov chains Y → X → Z) and a, b ≥ 0 are reals, then t ↦ a f₁(t) + b f₂(t) is a subadditive generator.
-/

theorem mutual_f_information_subadditive_add_mul (f₁ f₂ : ℝ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h₁ : mutual_f_information_subadditive f₁)
    (h₂ : mutual_f_information_subadditive f₂) :
    mutual_f_information_subadditive (fun t => a * f₁ t + b * f₂ t) := by
  intro X Y Z _ _ _ pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
  have e₁ := h₁ X Y Z pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
  have e₂ := h₂ X Y Z pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
  have hlin : ∀ {WW : Type} [Fintype WW] (qq : X → WW → ℝ),
      mutual_f_information (fun t => a * f₁ t + b * f₂ t) qq =
        a * mutual_f_information f₁ qq + b * mutual_f_information f₂ qq := by
    intro WW _ qq
    rw [mutual_f_information_add (fun t => a * f₁ t) (fun t => b * f₂ t),
      mutual_f_information_const_mul, mutual_f_information_const_mul]
  rw [hlin, hlin, hlin]
  nlinarith [mul_le_mul_of_nonneg_left e₁ ha, mul_le_mul_of_nonneg_left e₂ hb]
