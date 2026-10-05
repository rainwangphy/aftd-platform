import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCost
import AFTD.Kb.GameTheoryEconomics.GpaSimplex
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaUStarLeIndep

/-!
# gpa_lhs_upper

Topic: mechanism_design   Node: 340e6e20c397

Upper bound on the simplex: u*(σ) - h(σ) ≤ 1 - 1/α + 1/k for every σ ∈ Δ_k, where α ≥ 1 bounds every independent set.
-/

open Finset in
/-- Upper bound on the simplex: `u*(σ) - h(σ) ≤ 1 - 1/α + 1/k` for every `σ ∈ Δ_k`, where `α ≥ 1` bounds every independent set. -/
lemma gpa_lhs_upper {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (a : ℕ) (ha : 1 ≤ a) (hα : ∀ S, gpa_indep G S → S.card ≤ a)
    (σ : Fin k → ℝ) (hσ : σ ∈ gpa_simplex k) :
    gpa_uStar (gpa_adjMat G) σ - gpa_cost σ ≤ 1 - 1 / (a : ℝ) + 1 / (k : ℝ) := by
  obtain ⟨hnn, hsum⟩ := hσ
  obtain ⟨P, hP, hle⟩ := gpa_uStar_le_indep G σ hnn
  set M := ‖σ‖ with hM
  have hcoord : ∀ i, σ i ≤ M := fun i => by
    have := norm_le_pi_norm σ i
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn i)] at this
    exact this
  -- Σ_P σ ≤ 1
  have hP1 : ∑ i ∈ P, σ i ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
      (fun i _ _ => hnn i)
  -- Σ_P σ ≤ a M
  have hM0 : 0 ≤ M := norm_nonneg σ
  have hPa : ∑ i ∈ P, σ i ≤ (a : ℝ) * M := by
    have h1 : ∑ i ∈ P, σ i ≤ ∑ _i ∈ P, M := Finset.sum_le_sum (fun i _ => hcoord i)
    have h2 : (P.card : ℝ) ≤ a := by exact_mod_cast hα P hP
    simp at h1
    nlinarith
  have hcost : M - 1 / (k : ℝ) ≤ gpa_cost σ := le_max_left _ _
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  by_cases hcase : 1 ≤ (a : ℝ) * M
  · -- M ≥ 1/a
    have hMa : 1 / (a : ℝ) ≤ M := by
      rw [div_le_iff₀ hapos]; linarith
    linarith
  · replace hcase := not_le.mp hcase
    -- u* - h ≤ aM - M + 1/k = (a-1)M + 1/k ≤ (a-1)/a + 1/k
    have hkey : ((a : ℝ) - 1) * M ≤ 1 - 1 / (a : ℝ) := by
      have hMlt : M < 1 / (a : ℝ) := by
        rw [lt_div_iff₀ hapos]; linarith
      have : ((a : ℝ) - 1) * M ≤ ((a : ℝ) - 1) * (1 / a) :=
        mul_le_mul_of_nonneg_left hMlt.le (by linarith)
      have e : ((a : ℝ) - 1) * (1 / a) = 1 - 1 / (a : ℝ) := by field_simp
      linarith
    nlinarith
