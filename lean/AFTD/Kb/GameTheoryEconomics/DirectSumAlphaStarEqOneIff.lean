import AFTD.Prelude

/-!
# direct_sum_alpha_star_eq_one_iff

Topic: general_equilibrium   Node: cad79637dccb

Provenance: helper lemma. scout/2610-29731-computing-the-nucleon-of-matching-games.md:1163

For positive weights W_j > 0 and parameters 0 < r_j ≤ 1 on a nonempty finite index set M, the direct-sum calibration ratio α* = (∑_{j ∈ M} W_j) / (∑_{j ∈ M} W_j / r_j) equals 1 if and only if r_j = 1 for all j ∈ M.
-/

/-- The direct-sum calibration optimum equals 1 iff all component guarantees equal 1. -/
theorem direct_sum_alpha_star_eq_one_iff
    {M : Type*} [DecidableEq M] [Fintype M]
    (W : M → ℝ) (r : M → ℝ)
    (hM : (Finset.univ : Finset M).Nonempty)
    (hW : ∀ j, 0 < W j)
    (hr : ∀ j, 0 < r j ∧ r j ≤ 1) :
    let W_bar := Finset.univ.sum W
    let denom := Finset.univ.sum (fun j => W j / r j)
    (W_bar / denom = 1 ↔ ∀ j : M, r j = 1) := by
  intro W_bar denom
  have h_le : ∀ j ∈ Finset.univ, W j ≤ W j / r j := by
    intro j _
    have hrpos : 0 < r j := (hr j).1
    have hrle : r j ≤ 1 := (hr j).2
    have hWpos : 0 < W j := hW j
    rw [le_div_iff₀ hrpos]
    nlinarith
  have h_denom_pos : 0 < denom := by
    obtain ⟨j0, hj0⟩ := hM
    apply Finset.sum_pos'
    · intro j _
      exact div_nonneg (le_of_lt (hW j)) (le_of_lt (hr j).1)
    · exact ⟨j0, hj0, div_pos (hW j0) (hr j0).1⟩
  have h_div_eq : W_bar / denom = 1 ↔ W_bar = denom := div_eq_one_iff_eq (ne_of_gt h_denom_pos)
  rw [h_div_eq]
  dsimp [W_bar, denom]
  rw [Finset.sum_eq_sum_iff_of_le h_le]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro j
  have hr0 : r j ≠ 0 := ne_of_gt (hr j).1
  have hw0 : W j ≠ 0 := ne_of_gt (hW j)
  rw [eq_comm, div_eq_iff hr0, eq_comm]
  rw [mul_right_eq_self₀]
  simp [hw0]
