import AFTD.Prelude

/-!
# postage_stamp_number_neg_two_of_odd_sum_repr

Topic: elementary_number_theory   Node: b54808b91592

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

An h-fold sum of elements of {a, a+x, a+y} (x, y, x-y nonzero) equals h·a + s·x + t·y with s + t ≤ h.
-/

theorem postage_stamp_number_neg_two_of_odd_sum_repr
    (h : ℕ) (a x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (f : Fin h → ℤ) (hf : ∀ i, f i ∈ ({a, a + x, a + y} : Finset ℤ)) :
    ∃ s t : ℕ, s + t ≤ h ∧ ∑ i, f i = h * a + s * x + t * y := by
  refine ⟨(Finset.univ.filter (fun i : Fin h => f i = a + x)).card,
          (Finset.univ.filter (fun i : Fin h => f i = a + y)).card, ?_, ?_⟩
  · have hdisj : Disjoint (Finset.univ.filter (fun i : Fin h => f i = a + x))
        (Finset.univ.filter (fun i : Fin h => f i = a + y)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_filter] at hi1 hi2
      omega
    calc (Finset.univ.filter (fun i : Fin h => f i = a + x)).card +
        (Finset.univ.filter (fun i : Fin h => f i = a + y)).card
        = (Finset.univ.filter (fun i : Fin h => f i = a + x) ∪
           Finset.univ.filter (fun i : Fin h => f i = a + y)).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = h := by simp
  · have hpt : ∀ i : Fin h, f i = a + (if f i = a + x then x else 0) + (if f i = a + y then y else 0) := by
      intro i
      have hmem := hf i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hax : ¬ (a = a + x) := by omega
      have hay : ¬ (a = a + y) := by omega
      have hxy' : ¬ (a + x = a + y) := by omega
      have hyx' : ¬ (a + y = a + x) := by omega
      rcases hmem with h1 | h1 | h1
      · subst h1; simp [hax, hay]
      · rw [h1]; simp [hxy']
      · rw [h1]; simp [hyx']
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    simp only [Finset.sum_add_distrib]
    have h1 : (∑ i : Fin h, a) = h * a := by simp [Finset.sum_const]
    have h2 : (∑ i : Fin h, (if f i = a + x then x else 0)) =
        (Finset.univ.filter (fun i : Fin h => f i = a + x)).card * x := by
      rw [← Finset.sum_filter]; simp [Finset.sum_const]
    have h3 : (∑ i : Fin h, (if f i = a + y then y else 0)) =
        (Finset.univ.filter (fun i : Fin h => f i = a + y)).card * y := by
      rw [← Finset.sum_filter]; simp [Finset.sum_const]
    rw [h1, h2, h3]
