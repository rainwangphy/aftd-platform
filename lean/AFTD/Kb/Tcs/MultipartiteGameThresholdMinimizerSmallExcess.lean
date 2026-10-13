import AFTD.Prelude

/-!
# multipartite_game_threshold_minimizer_small_excess

Topic: combinatorics   Node: 56d5fe571c00

Provenance: formalization of a published result. Source: arXiv:2610.12508 (The Game Chromatic Number of Complete Multipartite Graphs with Triples), Lemma 2.2.

Let A ≥ 1, D ≥ 3 and r₁ ≥ … ≥ r_D ≥ 4 be integers, R_j = r₁ + … + r_j (R₀ = 0), q_j = ⌈max(R_j − A + 1, 0)/2⌉ and F_j = 2A + 2D − 2j − 3 + q_j. Then some index i ∈ {0, …, D−2} attains min_{0≤k≤D−2} F_k and has q_i ≤ 1.
-/

theorem multipartite_game_threshold_minimizer_small_excess (A D : ℕ) (r : ℕ → ℕ) (hA : 1 ≤ A)
    (hD : 3 ≤ D) (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D → r j ≤ r i) (h4 : 4 ≤ r D) :
    ∃ i ≤ D - 2,
      (∀ k ≤ D - 2,
        2 * A + 2 * D - 2 * i - 3 + ((∑ j ∈ Finset.Icc 1 i, r j) + 1 - A + 1) / 2 ≤
          2 * A + 2 * D - 2 * k - 3 + ((∑ j ∈ Finset.Icc 1 k, r j) + 1 - A + 1) / 2) ∧
      ((∑ j ∈ Finset.Icc 1 i, r j) + 1 - A + 1) / 2 ≤ 1 := by
  classical
  let F : ℕ → ℕ := fun k =>
    2 * A + 2 * D - 2 * k - 3 + ((∑ j ∈ Finset.Icc 1 k, r j) + 1 - A + 1) / 2
  let p : ℕ → Prop := fun n => n ≤ D - 2 ∧ ∀ k ≤ D - 2, F n ≤ F k
  have hex : ∃ n, p n := by
    have hne : (Finset.Iic (D - 2)).Nonempty := ⟨0, Finset.mem_Iic.2 (Nat.zero_le _)⟩
    obtain ⟨n, hn, hmin⟩ := Finset.exists_min_image (Finset.Iic (D - 2)) F hne
    simp only [Finset.mem_Iic] at hn hmin
    exact ⟨n, hn, hmin⟩
  let i := Nat.find hex
  have hpi : p i := Nat.find_spec hex
  have hqi : ((∑ j ∈ Finset.Icc 1 i, r j) + 1 - A + 1) / 2 ≤ 1 := by
    by_contra! hq
    have hi1 : 1 ≤ i := by
      by_contra! hi0
      have hi_eq : i = 0 := by omega
      rw [hi_eq] at hq
      simp only [Finset.Icc_eq_empty_of_lt (by decide : 1 > 0), Finset.sum_empty] at hq
      omega
    have hr : 4 ≤ r i := by
      have : r D ≤ r i := hmono i D hi1 (by omega) (by omega)
      omega
    have hsum : ∑ j ∈ Finset.Icc 1 i, r j = (∑ j ∈ Finset.Icc 1 (i - 1), r j) + r i := by
      have : Finset.Icc 1 i = insert i (Finset.Icc 1 (i - 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [this, Finset.sum_insert]
      · ring
      · simp; omega
    have hF_le : F (i - 1) ≤ F i := by
      dsimp [F]
      rw [hsum]
      omega
    have hpi_prev : p (i - 1) := by
      refine ⟨by omega, fun k hk => ?_⟩
      exact le_trans hF_le (hpi.2 k hk)
    have hnot : ¬ p (i - 1) := Nat.find_min hex (by omega)
    exact hnot hpi_prev
  exact ⟨i, hpi.1, hpi.2, hqi⟩
