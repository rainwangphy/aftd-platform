import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe

/-!
# postage_stamp_basis_range_ge_of_mod_four_eq_two

Topic: elementary_number_theory   Node: 48f34cc9b4b0

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for n), proof of Theorem 3.3 (the extremal basis {−w, w, w + 1}); serves postage_stamp_number_neg_two_eq_of_mod_four_eq_two.

For h = 4w − 2 (w ≥ 1), the set A = {−w, w, w + 1} satisfies n_h(A) ≥ (w + 1)h = (h² + 6h)/4.
-/

theorem postage_stamp_basis_range_ge_of_mod_four_eq_two_helper (w m : ℕ) (hw : 1 ≤ w) (hm : m ≤ (w + 1) * (4 * w - 2)) :
    int_mem_h_fold_sumset (4 * w - 2) {-(w : ℤ), (w : ℤ), (w : ℤ) + 1} (m : ℤ) := by
  let h := 4 * w - 2
  let X := m + h * w
  have h_cases : ∃ u s t : ℕ, u + s + t = h ∧
      -(u : ℤ) * (w : ℤ) + (s : ℤ) * (w : ℤ) + (t : ℤ) * ((w : ℤ) + 1) = (m : ℤ) := by
    rcases le_total (X / (2 * w)) h with hle | hle
    · have hw_pos : 0 < 2 * w := by omega
      have h2w : 2 ≤ 4 * w := by omega
      have hX_ge : h * w ≤ X := by dsimp [X]; omega
      let ell := X / (2 * w)
      let t := X % (2 * w)
      have hdiv : 2 * w - 1 ≤ ell := by
        dsimp [ell]
        rw [Nat.le_div_iff_mul_le hw_pos]
        have : (2 * w - 1) * (2 * w) = h * w := by
          zify [show 1 ≤ 2 * w by omega, h2w]
          dsimp [h]; rw [Nat.cast_sub h2w]; push_cast; ring
        rw [this]
        exact hX_ge
      have ht_lt : t < 2 * w := Nat.mod_lt X hw_pos
      have ht_le : t ≤ ell := by omega
      have hell_le : ell ≤ h := hle
      let u := h - ell
      let s := ell - t
      refine ⟨u, s, t, by omega, ?_⟩
      have hu_cast : (u : ℤ) = (h : ℤ) - (ell : ℤ) := by
        dsimp [u]; exact Nat.cast_sub hell_le
      have hs_cast : (s : ℤ) = (ell : ℤ) - (t : ℤ) := by
        dsimp [s]; exact Nat.cast_sub ht_le
      have hX_eq : X = 2 * w * ell + t := by
        dsimp [ell, t]
        exact (Nat.div_add_mod X (2 * w)).symm
      have hX_cast : (X : ℤ) = 2 * (w : ℤ) * (ell : ℤ) + (t : ℤ) := by
        exact_mod_cast hX_eq
      have hX_def : (X : ℤ) = (m : ℤ) + (h : ℤ) * (w : ℤ) := by
        show ((m + h * w : ℕ) : ℤ) = (m : ℤ) + (h : ℤ) * (w : ℤ)
        push_cast; rfl
      calc -(u : ℤ) * (w : ℤ) + (s : ℤ) * (w : ℤ) + (t : ℤ) * ((w : ℤ) + 1)
        _ = (-(u : ℤ) + (s : ℤ) + (t : ℤ)) * (w : ℤ) + (t : ℤ) := by ring
        _ = (-((h : ℤ) - (ell : ℤ)) + ((ell : ℤ) - (t : ℤ)) + (t : ℤ)) * (w : ℤ) + (t : ℤ) := by rw [hu_cast, hs_cast]
        _ = (2 * (ell : ℤ) - (h : ℤ)) * (w : ℤ) + (t : ℤ) := by ring
        _ = 2 * (w : ℤ) * (ell : ℤ) + (t : ℤ) - (h : ℤ) * (w : ℤ) := by ring
        _ = (X : ℤ) - (h : ℤ) * (w : ℤ) := by rw [← hX_cast]
        _ = (m : ℤ) := by rw [hX_def]; ring
    · have hw_pos : 0 < 2 * w := by omega
      have hm' : m ≤ (w + 1) * h := hm
      have : (w + 1) * h + h * w = 2 * w * h + h := by ring
      have hX_le : X ≤ 2 * w * h + h := by dsimp [X]; linarith
      have hX_ge : 2 * w * h ≤ X := by
        have := (Nat.le_div_iff_mul_le hw_pos).mp hle
        linarith
      let t := X - 2 * w * h
      have ht_le : t ≤ h := by omega
      let s := h - t
      refine ⟨0, s, t, by omega, ?_⟩
      have hs_cast : (s : ℤ) = (h : ℤ) - (t : ℤ) := by
        dsimp [s]; exact Nat.cast_sub ht_le
      have ht_cast : (t : ℤ) = (X : ℤ) - 2 * (w : ℤ) * (h : ℤ) := by
        dsimp [t]
        rw [Nat.cast_sub hX_ge]
        push_cast
        rfl
      have hX_def : (X : ℤ) = (m : ℤ) + (h : ℤ) * (w : ℤ) := by
        show ((m + h * w : ℕ) : ℤ) = (m : ℤ) + (h : ℤ) * (w : ℤ)
        push_cast; rfl
      rw [hs_cast, ht_cast, hX_def]
      ring
  obtain ⟨u, s, t, h_sum, h_val⟩ := h_cases
  have hl := int_mem_h_fold_sumset_of_list {-(w : ℤ), (w : ℤ), (w : ℤ) + 1}
    (List.replicate u (-(w : ℤ)) ++ List.replicate s (w : ℤ) ++ List.replicate t ((w : ℤ) + 1)) (by
      intro x hx
      simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> simp)
  have hlen : (List.replicate u (-(w : ℤ)) ++ List.replicate s (w : ℤ) ++ List.replicate t ((w : ℤ) + 1)).length = h := by
    simp; omega
  rw [hlen] at hl
  convert hl using 1
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
  rw [← h_val]
  ring

theorem postage_stamp_basis_range_ge_of_mod_four_eq_two (w : ℕ) (hw : 1 ≤ w) :
    (w + 1) * (4 * w - 2) ≤ postage_stamp_basis_range (4 * w - 2) {-(w : ℤ), (w : ℤ), (w : ℤ) + 1} := by
  apply le_csSup
  · refine ⟨(4 * w - 2) * (w + 1), fun n hn => ?_⟩
    have hn_in : int_mem_h_fold_sumset (4 * w - 2) {-(w : ℤ), (w : ℤ), (w : ℤ) + 1} (n : ℤ) := hn n le_rfl
    have h_le := int_mem_h_fold_sumset_le_of_forall_le (4 * w - 2) {-(w : ℤ), (w : ℤ), (w : ℤ) + 1} ((w : ℤ) + 1) (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (n : ℤ) hn_in
    exact_mod_cast h_le
  · intro m hm
    exact postage_stamp_basis_range_ge_of_mod_four_eq_two_helper w m hw hm
