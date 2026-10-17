import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe

/-!
# postage_stamp_basis_range_ge_of_mod_four_eq_zero

Topic: elementary_number_theory   Node: e50ac2e0afce

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for n), proof of Theorem 3.4 (the extremal basis {−(w−1), w, w+2}); serves postage_stamp_number_neg_two_eq_of_mod_four_eq_zero.

For h = 4w with w ≥ 2, the set A = {−(w − 1), w, w + 2} satisfies n_h(A) ≥ w(4w + 6) = (h² + 6h)/4.
-/

theorem postage_stamp_basis_range_ge_of_mod_four_eq_zero_helper (w m : ℕ) (hw : 2 ≤ w) (hm : m ≤ w * (4 * w + 6)) :
    int_mem_h_fold_sumset (4 * w) {-((w : ℤ) - 1), (w : ℤ), (w : ℤ) + 2} (m : ℤ) := by
  let h := 4 * w
  let X := m + h * (w - 1)
  have hw1 : 1 ≤ w := by omega
  have h1 : 1 ≤ 2 * w := by omega
  have h2 : 2 ≤ 2 * w := by omega
  have h3 : 4 * w ≤ 4 * w^2 := by nlinarith
  have h_sub : 4 * w * (w - 1) = 4 * w^2 - 4 * w := by
    rw [Nat.mul_sub_left_distrib, mul_assoc, ← sq, mul_one]
  have hXmin : 4 * w^2 - 4 * w ≤ X := by
    dsimp [X, h]; rw [h_sub]; omega
  have hX_cast : (X : ℤ) = (m : ℤ) + 4 * (w : ℤ) * ((w : ℤ) - 1) := by
    dsimp [X, h]; push_cast [Nat.cast_sub hw1]; rfl
  have hm_cast : (m : ℤ) ≤ (w : ℤ) * (4 * (w : ℤ) + 6) := by exact_mod_cast hm
  have hXmax_z : (X : ℤ) ≤ 8 * (w : ℤ)^2 + 2 * (w : ℤ) := by
    rw [hX_cast]; nlinarith
  have hXmax : X ≤ 8 * w^2 + 2 * w := by exact_mod_cast hXmax_z
  have h_cases_exist : ∃ u s t : ℕ, u + s + t = h ∧
      -(u : ℤ) * ((w : ℤ) - 1) + (s : ℤ) * (w : ℤ) + (t : ℤ) * ((w : ℤ) + 2) = (m : ℤ) := by
    let P := fun k => k % 2 = X % 2 ∧ (2 * w - 1) * k ≤ X
    have : DecidablePred P := Classical.decPred _
    have h_base : ∃ k, 2 * w - 2 ≤ k ∧ k ≤ h ∧ P k := by
      rcases Nat.mod_two_eq_zero_or_one X with hX | hX
      · refine ⟨2 * w - 2, le_rfl, by omega, ?_⟩
        dsimp [P]
        refine ⟨by omega, ?_⟩
        have : (2 * w - 1) * (2 * w - 2) ≤ 4 * w^2 - 4 * w := by
          zify [h1, h2, h3]; ring_nf; linarith
        omega
      · refine ⟨2 * w - 1, by omega, by omega, ?_⟩
        dsimp [P]
        refine ⟨by omega, ?_⟩
        have : (2 * w - 1) * (2 * w - 1) = 4 * w^2 - 4 * w + 1 := by
          zify [h1, h3]; ring
        omega
    obtain ⟨k0, hk0_ge, hk0_le, hk0_P⟩ := h_base
    let ell := Nat.findGreatest P h
    have hell_P : P ell := Nat.findGreatest_spec hk0_le hk0_P
    have hell_le : ell ≤ h := Nat.findGreatest_le h
    have hk0_le_ell : k0 ≤ ell := Nat.le_findGreatest hk0_le hk0_P
    have hell_ge : 2 * w - 2 ≤ ell := by omega
    have h_high : X ≤ (2 * w + 1) * ell := by
      by_contra! h_gt
      have h_ell_plus2_le_h : ell + 2 ≤ h := by
        by_contra! h_not
        have h_cases : ell = 4 * w ∨ ell = 4 * w - 1 := by omega
        have h_gt_z : (2 * (w : ℤ) + 1) * (ell : ℤ) < (X : ℤ) := by exact_mod_cast h_gt
        rcases h_cases with h_ell | h_ell
        · have : (ell : ℤ) = 4 * (w : ℤ) := by exact_mod_cast h_ell
          nlinarith
        · have hell_z : (ell : ℤ) = 4 * (w : ℤ) - 1 := by
            have : 1 ≤ 4 * w := by omega
            rw [h_ell, Nat.cast_sub this]; push_cast; rfl
          have hX_ge_z : 8 * (w : ℤ)^2 + 2 * (w : ℤ) ≤ (X : ℤ) := by nlinarith
          have hX_eq_z : (X : ℤ) = 8 * (w : ℤ)^2 + 2 * (w : ℤ) := by omega
          have hX_even : (X : ℤ) % 2 = 0 := by
            rw [hX_eq_z]
            have : 8 * (w : ℤ)^2 + 2 * (w : ℤ) = 2 * (4 * (w : ℤ)^2 + (w : ℤ)) := by ring
            rw [this, Int.mul_emod_right]
          have hell_odd : (ell : ℤ) % 2 = 1 := by
            rw [hell_z]
            have : 4 * (w : ℤ) - 1 = 2 * (2 * (w : ℤ) - 1) + 1 := by ring
            rw [this]
            omega
          have h_mod_eq : (ell : ℤ) % 2 = (X : ℤ) % 2 := by
            have h_e1 : (ell : ℤ) % 2 = ((ell % 2 : ℕ) : ℤ) := by omega
            have h_e2 : (X : ℤ) % 2 = ((X % 2 : ℕ) : ℤ) := by omega
            have h_e3 : ell % 2 = X % 2 := hell_P.1
            rw [h_e1, h_e2, h_e3]
          omega
      have h_P_plus2 : P (ell + 2) := by
        dsimp [P]
        refine ⟨by omega, ?_⟩
        by_cases h_ell_ge : 2 * w - 1 ≤ ell
        · have : (2 * w - 1) * (ell + 2) ≤ (2 * w + 1) * ell := by
            zify [h1] at h_ell_ge ⊢
            nlinarith
          omega
        · have hell_eq : ell = 2 * w - 2 := by omega
          have h_gt' : (2 * (w : ℤ) + 1) * (ell : ℤ) < (X : ℤ) := by exact_mod_cast h_gt
          have hell_eq' : (ell : ℤ) = 2 * (w : ℤ) - 2 := by
            rw [hell_eq, Nat.cast_sub h2]; push_cast; rfl
          rw [hell_eq'] at h_gt'
          have h_exp : (2 * (w : ℤ) + 1) * (2 * (w : ℤ) - 2) = 4 * (w : ℤ)^2 - 2 * (w : ℤ) - 2 := by ring
          rw [h_exp] at h_gt'
          have h_even : (X : ℤ) % 2 = 0 := by
            have h_e1 : (X : ℤ) % 2 = ((X % 2 : ℕ) : ℤ) := by omega
            have h_e2 : ell % 2 = 0 := by rw [hell_eq]; omega
            have h_e3 := hell_P.1
            omega
          have : (4 * (w : ℤ)^2 - 2 * (w : ℤ) : ℤ) % 2 = 0 := by
            have : 4 * (w : ℤ)^2 - 2 * (w : ℤ) = 2 * (2 * (w : ℤ)^2 - (w : ℤ)) := by ring
            rw [this, Int.mul_emod_right]
          have h_X_ge : 4 * (w : ℤ)^2 - 2 * (w : ℤ) ≤ (X : ℤ) := by omega
          have : (ell + 2) = 2 * w := by omega
          rw [this]
          have h_lhs : (((2 * w - 1) * (2 * w) : ℕ) : ℤ) = 4 * (w : ℤ)^2 - 2 * (w : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_sub h1]
            push_cast; ring
          exact_mod_cast (h_lhs.symm ▸ h_X_ge)
      have h_contr := Nat.findGreatest_is_greatest (by omega : ell < ell + 2) h_ell_plus2_le_h
      exact h_contr h_P_plus2
    have h_mod1 : (2 * w - 1) % 2 = 1 := by omega
    have h_mod : ((2 * w - 1) * ell) % 2 = ell % 2 := by
      rw [Nat.mul_mod, h_mod1, one_mul, Nat.mod_mod]
    have heven : (X - (2 * w - 1) * ell) % 2 = 0 := by
      let Y := (2 * w - 1) * ell
      change (X - Y) % 2 = 0
      have hY : Y ≤ X := hell_P.2
      have hY_mod : Y % 2 = X % 2 := by rw [h_mod, hell_P.1]
      omega
    let t := (X - (2 * w - 1) * ell) / 2
    have ht_eq : 2 * t = X - (2 * w - 1) * ell := by
      dsimp [t]; omega
    have ht_le : t ≤ ell := by
      have : 2 * t ≤ 2 * ell := by
        rw [ht_eq]
        have : ((X - (2 * w - 1) * ell : ℕ) : ℤ) ≤ 2 * (ell : ℤ) := by
          rw [Nat.cast_sub hell_P.2, Nat.cast_mul, Nat.cast_sub h1]
          have hX_ineq : (X : ℤ) ≤ (2 * (w : ℤ) + 1) * (ell : ℤ) := by exact_mod_cast h_high
          push_cast at hX_ineq ⊢
          nlinarith
        exact_mod_cast this
      omega
    let s := ell - t
    let u := h - ell
    have h_sum : u + s + t = h := by dsimp [u, s]; omega
    refine ⟨u, s, t, h_sum, ?_⟩
    have hu_cast : (u : ℤ) = (h : ℤ) - (ell : ℤ) := by
      dsimp [u]; exact Nat.cast_sub hell_le
    have hs_cast : (s : ℤ) = (ell : ℤ) - (t : ℤ) := by
      dsimp [s]; exact Nat.cast_sub ht_le
    have ht_cast : 2 * (t : ℤ) = (X : ℤ) - (2 * (w : ℤ) - 1) * (ell : ℤ) := by
      have : ((2 * t : ℕ) : ℤ) = ((X - (2 * w - 1) * ell : ℕ) : ℤ) := by exact_mod_cast ht_eq
      push_cast at this
      rw [Nat.cast_sub hell_P.2, Nat.cast_mul, Nat.cast_sub h1] at this
      push_cast at this
      exact this
    have hX_comb : (X : ℤ) = (m : ℤ) + (h : ℤ) * ((w : ℤ) - 1) := by
      dsimp [X, h]; push_cast [Nat.cast_sub hw1]; rfl
    calc -(u : ℤ) * ((w : ℤ) - 1) + (s : ℤ) * (w : ℤ) + (t : ℤ) * ((w : ℤ) + 2)
      _ = -((h : ℤ) - (ell : ℤ)) * ((w : ℤ) - 1) + ((ell : ℤ) - (t : ℤ)) * (w : ℤ) + (t : ℤ) * ((w : ℤ) + 2) := by rw [hu_cast, hs_cast]
      _ = -((h : ℤ) - (ell : ℤ)) * ((w : ℤ) - 1) + (ell : ℤ) * (w : ℤ) + 2 * (t : ℤ) := by ring
      _ = -((h : ℤ) - (ell : ℤ)) * ((w : ℤ) - 1) + (ell : ℤ) * (w : ℤ) + ((X : ℤ) - (2 * (w : ℤ) - 1) * (ell : ℤ)) := by rw [ht_cast]
      _ = (X : ℤ) - (h : ℤ) * ((w : ℤ) - 1) := by ring
      _ = (m : ℤ) := by rw [hX_comb]; ring
  obtain ⟨u, s, t, h_sum, h_val⟩ := h_cases_exist
  have hl := int_mem_h_fold_sumset_of_list {-((w : ℤ) - 1), (w : ℤ), (w : ℤ) + 2}
    (List.replicate u (-((w : ℤ) - 1)) ++ List.replicate s (w : ℤ) ++ List.replicate t ((w : ℤ) + 2)) (by
      intro x hx; simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> simp)
  have hlen : (List.replicate u (-((w : ℤ) - 1)) ++ List.replicate s (w : ℤ) ++ List.replicate t ((w : ℤ) + 2)).length = 4 * w := by
    simp; omega
  rw [hlen] at hl
  convert hl using 1
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
  rw [← h_val]
  ring

theorem postage_stamp_basis_range_ge_of_mod_four_eq_zero (w : ℕ) (hw : 2 ≤ w) :
    w * (4 * w + 6) ≤ postage_stamp_basis_range (4 * w) {-((w : ℤ) - 1), (w : ℤ), (w : ℤ) + 2} := by
  apply le_csSup
  · refine ⟨(4 * w) * (w + 2), fun n hn => ?_⟩
    have hn_in : int_mem_h_fold_sumset (4 * w) {-((w : ℤ) - 1), (w : ℤ), (w : ℤ) + 2} (n : ℤ) := hn n le_rfl
    have h_le := int_mem_h_fold_sumset_le_of_forall_le (4 * w) {-((w : ℤ) - 1), (w : ℤ), (w : ℤ) + 2} ((w : ℤ) + 2) (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (n : ℤ) hn_in
    exact_mod_cast h_le
  · intro m hm
    exact postage_stamp_basis_range_ge_of_mod_four_eq_zero_helper w m hw hm
