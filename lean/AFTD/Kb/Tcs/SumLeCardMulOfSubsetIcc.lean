import AFTD.Prelude

/-!
# sum_le_card_mul_of_subset_Icc

Topic: combinatorics   Node: b70477287b13

Provenance: helper lemma. arXiv:2610.34372, Proof of Lemma 2.1

If A is a subset of {1, ..., N} and B is a subset of A, then the sum of the elements of B is at most the cardinality of A multiplied by N.
-/

/-- Every subset sum of a subset of {1, ..., N} of size m is at most m * N. -/
theorem sum_le_card_mul_of_subset_Icc (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (B : Finset ℕ) (hB : B ⊆ A) : B.sum id ≤ A.card * N := by
  have h1 : ∀ x ∈ B, id x ≤ N := fun x hx => (Finset.mem_Icc.mp (hA (hB hx))).2
  exact (Finset.sum_le_card_nsmul B id N h1).trans (Nat.mul_le_mul_right N (Finset.card_le_card hB))
