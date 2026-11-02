import AFTD.Prelude

/-!
# arrangement3_sum_entries

Topic: combinatorics   Node: 1ec3423c07bc

Provenance: helper lemma. arXiv:2610.38386, Section 5.1

The sum of all entries in any 3 × 3 arrangement of the integers 1 through 9 (without repetition) is 45.
-/

/-- The sum of all entries of an order 3 arrangement S is 45. -/
lemma arrangement3_sum_entries (S : Fin 3 × Fin 3 ≃ Fin 9) :
    ∑ i : Fin 3, ∑ j : Fin 3, ((S (i, j)).val + 1 : ℤ) = 45 := by
  rw [← Fintype.sum_prod_type (fun p : Fin 3 × Fin 3 => ((S p).val + 1 : ℤ))]
  rw [Equiv.sum_comp S (fun k : Fin 9 => ((k : ℤ) + 1))]
  rfl
