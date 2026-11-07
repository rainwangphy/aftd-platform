import AFTD.Prelude

/-!
# pm_one_rows_differ_in_half_exists_solution

Topic: combinatorics   Node: 0e5ea0566089

Provenance: helper lemma. arXiv:2611.00468 (The symbolic pfaffian method I), Lemma 2.1, the linear-algebra step (the proof differs from the paper's: an explicit solution instead of a rank argument)

Let k ≥ 1 and let A : ι → Fin (2k) → ℝ be a finite family of rows with entries ±1. If any two distinct rows differ in exactly k coordinates, then some x : Fin (2k) → ℝ has ∑_j A i j * x j = 1 for every i.
-/

theorem pm_one_rows_differ_in_half_exists_solution {k : ℕ} (hk : 1 ≤ k) {ι : Type*} [Finite ι]
    (A : ι → Fin (2 * k) → ℝ) (hA : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hrows : ∀ i i', A i ≠ A i' → (Finset.univ.filter fun j => A i j ≠ A i' j).card = k) :
    ∃ x : Fin (2 * k) → ℝ, ∀ i, ∑ j, A i j * x j = 1 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set S : Finset (Fin (2 * k) → ℝ) := Finset.univ.image A with hS
  refine ⟨fun j => (1 / (2 * k : ℝ)) * ∑ a ∈ S, a j, fun i => ?_⟩
  have hk' : (0 : ℝ) < 2 * k := by positivity
  -- inner products of rows
  have hprod : ∀ i' j, A i j * A i' j = if A i j = A i' j then 1 else -1 := by
    intro i' j
    rcases hA i j with h | h <;> rcases hA i' j with h' | h' <;> rw [h, h'] <;> norm_num
  have hinner : ∀ a ∈ S, ∑ j, A i j * a j = if a = A i then (2 * k : ℝ) else 0 := by
    intro a ha
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp ha
    simp only [hprod]
    by_cases he : A i' = A i
    · rw [if_pos he]
      simp only [he, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      push_cast; ring
    · rw [if_neg he]
      have hc := hrows i i' (Ne.symm he)
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * k))))
        (fun j => A i j = A i' j)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have hc' : (Finset.univ.filter fun j => ¬ A i j = A i' j).card = k := by
        simpa only [ne_eq] using hc
      rw [hc'] at hsplit ⊢
      have : (Finset.univ.filter fun j => A i j = A i' j).card = k := by omega
      rw [this]; ring
  calc ∑ j, A i j * ((1 / (2 * k : ℝ)) * ∑ a ∈ S, a j)
      = (1 / (2 * k : ℝ)) * ∑ a ∈ S, ∑ j, A i j * a j := by
        simp only [Finset.mul_sum]
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (1 / (2 * k : ℝ)) * ∑ a ∈ S, (if a = A i then (2 * k : ℝ) else 0) := by
        rw [Finset.sum_congr rfl hinner]
    _ = 1 := by
        rw [Finset.sum_ite_eq' S (A i), if_pos (Finset.mem_image_of_mem A (Finset.mem_univ i))]
        field_simp
