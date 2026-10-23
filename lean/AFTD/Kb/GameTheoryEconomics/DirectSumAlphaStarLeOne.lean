import AFTD.Prelude

/-!
# direct_sum_alpha_star_le_one

Topic: general_equilibrium   Node: 373af5476167

Provenance: helper lemma. scout/2610-29731-computing-the-nucleon-of-matching-games.md:1163

For positive weights W_j > 0 and parameters 0 < r_j ≤ 1 on a nonempty finite index set M, the direct-sum calibration ratio α* = (∑_{j ∈ M} W_j) / (∑_{j ∈ M} W_j / r_j) satisfies α* ≤ 1.
-/

/-- The direct-sum calibration optimum is at most 1 when guarantees are in (0, 1]. -/
theorem direct_sum_alpha_star_le_one
    {M : Type*} [DecidableEq M] [Fintype M]
    (W : M → ℝ) (r : M → ℝ)
    (hM : (Finset.univ : Finset M).Nonempty)
    (hW : ∀ j, 0 < W j)
    (hr : ∀ j, 0 < r j ∧ r j ≤ 1) :
    let W_bar := Finset.univ.sum W
    let denom := Finset.univ.sum (fun j => W j / r j)
    W_bar / denom ≤ 1 := by
  intro W_bar denom
  have h_le : ∀ j ∈ Finset.univ, W j ≤ W j / r j := by
    intro j _
    have hrpos : 0 < r j := (hr j).1
    have hrle : r j ≤ 1 := (hr j).2
    have hWpos : 0 < W j := hW j
    rw [le_div_iff₀ hrpos]
    nlinarith
  have h_sum_le : W_bar ≤ denom := Finset.sum_le_sum h_le
  have h_denom_pos : 0 < denom := by
    obtain ⟨j0, hj0⟩ := hM
    apply Finset.sum_pos'
    · intro j _
      exact div_nonneg (le_of_lt (hW j)) (le_of_lt (hr j).1)
    · exact ⟨j0, hj0, div_pos (hW j0) (hr j0).1⟩
  exact (div_le_one₀ h_denom_pos).mpr h_sum_le
