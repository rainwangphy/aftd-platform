import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumWBad
import AFTD.Kb.Tcs.ZeroSumBasisSeq
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# zero_sum_basis_seq_w_bad

Topic: combinatorics   Node: 2af3001654c3

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Lemma 3.1 (first part; the bound on w_r(n) is zero_sum_w_ge).

For n > 1 and r ≥ 1, the admissible sequence E_{r,n} (length 2r(n−1)) has no nonempty subsequence whose sum is ≡ 0 (mod n) but ≢ 0 (mod n²).
-/

theorem zero_sum_basis_seq_w_bad (r n : ℕ) (hn : 1 < n) :
    zero_sum_w_bad n (zero_sum_basis_seq r n) ∧ (zero_sum_basis_seq r n).length = 2 * r * (n - 1) := by
  have hpos : ∀ j : Fin r,
      ((zero_sum_basis_seq r n).map (fun a => max (a j) 0)).sum = ((n - 1 : ℕ) : ℤ) := by
    intro j
    simp [zero_sum_basis_seq, List.flatMap, List.sum_flatten, Function.comp_def, Pi.single_apply]
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
    have h1 : ∀ i : Fin r, max (if j = i then (1 : ℤ) else 0) 0 = if j = i then 1 else 0 := by
      intro i; split_ifs <;> simp
    have h2 : ∀ i : Fin r, max (-if j = i then (1 : ℤ) else 0) 0 = 0 := by
      intro i; split_ifs <;> simp
    simp [h1, h2]
  have hneg : ∀ j : Fin r,
      ((zero_sum_basis_seq r n).map (fun a => max (-a j) 0)).sum = ((n - 1 : ℕ) : ℤ) := by
    intro j
    simp [zero_sum_basis_seq, List.flatMap, List.sum_flatten, Function.comp_def, Pi.single_apply]
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
    have h1 : ∀ i : Fin r, max (if j = i then (1 : ℤ) else 0) 0 = if j = i then 1 else 0 := by
      intro i; split_ifs <;> simp
    have h2 : ∀ i : Fin r, max (-if j = i then (1 : ℤ) else 0) 0 = 0 := by
      intro i; split_ifs <;> simp
    simp [h1, h2]
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by push_cast [Nat.cast_sub hn.le]; ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    simp only [zero_sum_basis_seq, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append,
      List.mem_replicate] at ha
    obtain ⟨j, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩ := ha
    · refine ⟨j, ?_⟩
      simp only [Pi.single_eq_same]
      intro h
      have := Int.le_of_dvd one_pos h
      omega
    · refine ⟨j, ?_⟩
      simp only [Pi.neg_apply, Pi.single_eq_same]
      intro h
      have := Int.le_of_dvd one_pos ((Int.dvd_neg).mp h)
      omega
  · rintro I ⟨-, hdiv, j, hj⟩
    apply hj
    have hup : ∑ i ∈ I, (zero_sum_basis_seq r n).get i j ≤ ((n - 1 : ℕ) : ℤ) := by
      calc ∑ i ∈ I, (zero_sum_basis_seq r n).get i j
          ≤ ∑ i ∈ I, max ((zero_sum_basis_seq r n).get i j) 0 :=
            Finset.sum_le_sum (fun i _ => le_max_left _ _)
        _ ≤ ∑ i, max ((zero_sum_basis_seq r n).get i j) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => le_max_right _ _)
        _ = ((zero_sum_basis_seq r n).map (fun a => max (a j) 0)).sum := by
            simpa using Fin.sum_univ_fun_getElem (zero_sum_basis_seq r n) (fun a => max (a j) 0)
        _ = _ := hpos j
    have hlo : -((n - 1 : ℕ) : ℤ) ≤ ∑ i ∈ I, (zero_sum_basis_seq r n).get i j := by
      have : ∑ i ∈ I, -(zero_sum_basis_seq r n).get i j ≤ ((n - 1 : ℕ) : ℤ) := by
        calc ∑ i ∈ I, -(zero_sum_basis_seq r n).get i j
            ≤ ∑ i ∈ I, max (-(zero_sum_basis_seq r n).get i j) 0 :=
              Finset.sum_le_sum (fun i _ => le_max_left _ _)
          _ ≤ ∑ i, max (-(zero_sum_basis_seq r n).get i j) 0 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun i _ _ => le_max_right _ _)
          _ = ((zero_sum_basis_seq r n).map (fun a => max (-a j) 0)).sum := by
              simpa using Fin.sum_univ_fun_getElem (zero_sum_basis_seq r n) (fun a => max (-a j) 0)
          _ = _ := hneg j
      rw [Finset.sum_neg_distrib] at this
      linarith
    obtain ⟨k, hk⟩ := hdiv j
    rw [hk] at hup hlo ⊢
    rw [hcast] at hup hlo
    have hn' : (1 : ℤ) < n := by exact_mod_cast hn
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hk0, mul_zero]
    exact dvd_zero _
  · simp [zero_sum_basis_seq, List.length_flatMap]
    ring
