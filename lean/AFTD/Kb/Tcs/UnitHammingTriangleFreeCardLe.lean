import AFTD.Prelude
import AFTD.Kb.Tcs.UnitHammingTriangleFree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# unit_hamming_triangle_free_card_le

Topic: combinatorics   Node: 8f828dc63f13

Provenance: helper lemma. arXiv:2610.32789 Section 3.1

For every integer q ≥ 2 and every integer n ≥ 1, every finite set A : Finset (Fin n → Fin q) satisfying unit_hamming_triangle_free A satisfies A.card ≤ 2 * q ^ (n - 1).
-/

lemma unit_hamming_triangle_free_card_le_hammingDist_one (m q : ℕ) (x y : Fin (m + 1) → Fin q)
    (h_tail : Fin.tail x = Fin.tail y) (hne : x ≠ y) :
    hammingDist x y = 1 := by
  have h0 : x 0 ≠ y 0 := by
    intro h
    apply hne
    funext i
    induction' i using Fin.cases with j
    · exact h
    · exact congr_fun h_tail j
  have h_set : Finset.filter (fun i => x i ≠ y i) Finset.univ = {0} := by
    ext i
    induction' i using Fin.cases with j
    · simp [h0]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have hj : Fin.tail x j = Fin.tail y j := congr_fun h_tail j
      change x j.succ = y j.succ at hj
      simp [hj, Fin.succ_ne_zero]
  unfold hammingDist
  rw [h_set, Finset.card_singleton]

lemma unit_hamming_triangle_free_card_le_exists_three {α : Type*} [DecidableEq α]
    {s : Finset α} (h : 2 < s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h
  obtain ⟨x, hx⟩ := hne
  have hcard : 1 < (s \ {x}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hx), Finset.card_singleton]
    omega
  rw [Finset.one_lt_card] at hcard
  obtain ⟨y, hy, z, hz, hyz⟩ := hcard
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hy hz
  exact ⟨x, hx, y, hy.1, z, hz.1, Ne.symm hy.2, hyz, Ne.symm hz.2⟩

lemma unit_hamming_triangle_free_card_le_fiber_card_le_two (m q : ℕ)
    (A : Finset (Fin (m + 1) → Fin q)) (hA : unit_hamming_triangle_free A)
    (b : Fin m → Fin q) :
    {a ∈ A | Fin.tail a = b}.card ≤ 2 := by
  by_contra! h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz⟩ :=
    unit_hamming_triangle_free_card_le_exists_three h
  simp only [Finset.mem_filter] at hx hy hz
  have dxy : hammingDist x y = 1 :=
    unit_hamming_triangle_free_card_le_hammingDist_one m q x y (hx.2.trans hy.2.symm) hxy
  have dyz : hammingDist y z = 1 :=
    unit_hamming_triangle_free_card_le_hammingDist_one m q y z (hy.2.trans hz.2.symm) hyz
  have dxz : hammingDist x z = 1 :=
    unit_hamming_triangle_free_card_le_hammingDist_one m q x z (hx.2.trans hz.2.symm) hxz
  exact hA hx.1 hy.1 hz.1 hxy hyz hxz ⟨dxy, dyz, dxz⟩

/-- Upper bound on the size of a triangle-free subset in the unit-distance Hamming graph: |A| ≤ 2 * q^(n-1). -/
theorem unit_hamming_triangle_free_card_le (n q : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n)
    (A : Finset (Fin n → Fin q)) (hA : unit_hamming_triangle_free A) :
    A.card ≤ 2 * q ^ (n - 1) := by
  have _ := hq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have h_bound := Finset.card_le_mul_card_image (f := Fin.tail) A 2 (by
    intro b _
    exact unit_hamming_triangle_free_card_le_fiber_card_le_two m q A hA b)
  have h_img : (Finset.image Fin.tail A).card ≤ q ^ m := by
    calc (Finset.image Fin.tail A).card ≤ (Finset.univ : Finset (Fin m → Fin q)).card :=
          Finset.card_le_univ _
      _ = Fintype.card (Fin m → Fin q) := rfl
      _ = q ^ m := by simp
  have hm : m + 1 - 1 = m := rfl
  rw [hm]
  linarith
