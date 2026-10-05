import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCost
import AFTD.Kb.GameTheoryEconomics.GpaSimplex
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaNbrNonneg

/-!
# gpa_lhs_attain

Topic: mechanism_design   Node: 25957374f616

The bound 1 - 1/α + 1/k is attained on the simplex, by the uniform distribution on a maximum independent set I (1 ≤ |I| ≤ k).
-/

open Finset in
/-- The bound `1 - 1/α + 1/k` is attained on the simplex, by the uniform distribution on a maximum independent set `I` (`1 ≤ |I| ≤ k`). -/
lemma gpa_lhs_attain {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (I : Finset (Fin k)) (hI : gpa_indep G I) (hne : 1 ≤ I.card) (hk : I.card ≤ k) :
    ∃ σ ∈ gpa_simplex k,
      gpa_uStar (gpa_adjMat G) σ - gpa_cost σ = 1 - 1 / (I.card : ℝ) + 1 / (k : ℝ) := by
  classical
  set a : ℝ := (I.card : ℝ) with ha_def
  have haR : (1 : ℝ) ≤ a := by rw [ha_def]; exact_mod_cast hne
  have hapos : (0 : ℝ) < a := by linarith
  have hkR : a ≤ (k : ℝ) := by rw [ha_def]; exact_mod_cast hk
  let σ : Fin k → ℝ := fun i => if i ∈ I then 1 / a else 0
  have hσnn : ∀ i, 0 ≤ σ i := fun i => by
    simp only [σ]; split_ifs
    · exact div_nonneg zero_le_one hapos.le
    · exact le_refl 0
  have hσsum : ∑ i, σ i = 1 := by
    simp only [σ]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [← ha_def]; field_simp
  refine ⟨σ, ⟨hσnn, hσsum⟩, ?_⟩
  -- u*(σ) = 1
  have hu : gpa_uStar (gpa_adjMat G) σ = 1 := by
    unfold gpa_uStar
    have hterm : ∀ i, max (σ i - ∑ j, gpa_adjMat G i j * σ j) 0 = σ i := by
      intro i
      by_cases hi : i ∈ I
      · have hz : ∑ j, gpa_adjMat G i j * σ j = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj : j ∈ I
          · have : ¬ G.Adj i j := hI i hi j hj
            simp [gpa_adjMat, this]
          · simp [σ, hj]
        rw [hz, sub_zero]; exact max_eq_left (hσnn i)
      · have hnn := gpa_nbr_nonneg G σ hσnn i
        have h0 : σ i = 0 := by simp [σ, hi]
        rw [h0]
        exact max_eq_right (by linarith)
    simp_rw [hterm]
    exact hσsum
  -- ‖σ‖ = 1/a
  have hnorm : ‖σ‖ = 1 / a := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (div_nonneg zero_le_one hapos.le)).2
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hσnn i)]
      simp only [σ]; split_ifs
      · exact le_refl _
      · exact div_nonneg zero_le_one hapos.le
    · obtain ⟨i0, hi0⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
      have := norm_le_pi_norm σ i0
      rw [Real.norm_eq_abs, abs_of_nonneg (hσnn i0)] at this
      simpa [σ, hi0] using this
  have hcost : gpa_cost σ = 1 / a - 1 / (k : ℝ) := by
    unfold gpa_cost
    rw [hnorm]
    apply max_eq_left
    have hkpos : (0 : ℝ) < k := by linarith
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hapos hkR
  rw [hu, hcost]
  ring
