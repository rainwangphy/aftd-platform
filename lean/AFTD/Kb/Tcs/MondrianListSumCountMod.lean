import AFTD.Prelude

/-!
# mondrian_list_sum_count_mod

Topic: combinatorics   Node: 4108c94f53f1

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

If each integer list contribution is congruent modulo p to u when its predicate holds and to zero otherwise, their sum is congruent to u times the number satisfying the predicate.
-/

open scoped BigOperators

theorem mondrian_list_sum_count_mod (L : List (ℕ × ℕ × ℕ × ℕ))
    (p u : ℤ) (f : (ℕ × ℕ × ℕ × ℕ) → ℤ)
    (pred : (ℕ × ℕ × ℕ × ℕ) → Bool)
    (h : ∀ r ∈ L, p ∣ f r - if pred r then u else 0) :
    p ∣ (L.map f).sum - (L.countP pred : ℤ) * u := by
  induction L with
  | nil => simp
  | cons r L ih =>
    have hr := h r (by simp)
    have ht := ih (fun s hs => h s (by simp [hs]))
    have heq : ((r :: L).map f).sum - ((r :: L).countP pred : ℤ) * u =
        (f r - if pred r then u else 0) +
          ((L.map f).sum - (L.countP pred : ℤ) * u) := by
      simp only [List.map_cons, List.sum_cons, List.countP_cons]
      cases pred r <;> simp <;> ring
    rw [heq]
    exact dvd_add hr ht
