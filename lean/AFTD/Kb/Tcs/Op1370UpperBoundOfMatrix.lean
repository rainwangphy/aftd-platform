import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixBlockDetCardSumLeWidth
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_upper_bound_of_matrix

Topic: combinatorics   Node: 2b95b27d5de7

Provenance: helper lemma. arXiv:2611.12199, Section 2.2 (Theorem 2.1 implies Theorem 1.7)

Let n be a natural number. Suppose there are a field K, a matrix L with rows indexed by the subsets of Fin n and 2^(n-1) columns, and a matrix R with 2^(n-1) rows and columns indexed by the subsets of Fin n, such that L*R vanishes at every pair (A, B) of incomparable subsets (neither A ⊆ B nor B ⊆ A), and every principal submatrix of L*R on an uncomplemented family of subsets has nonzero determinant. Then for every t and families A_1, ..., A_t of subsets of Fin n, each uncomplemented and together strongly incomparable, the sizes of the A_i sum to at most 2^(n-1).
-/

/-- Hilton's strong-incomparability bound follows from the existence of the rank-2^(n-1) matrix of Theorem 2.1 (the paper's Section 2.2). -/
theorem op_1370_upper_bound_of_matrix (n : ℕ)
    (hM : ∃ (K : Type) (_ : Field K) (L : Matrix (Finset (Fin n)) (Fin (2 ^ (n - 1))) K)
      (R : Matrix (Fin (2 ^ (n - 1))) (Finset (Fin n)) K),
      (∀ A B : Finset (Fin n), ¬ A ⊆ B → ¬ B ⊆ A → (L * R) A B = 0) ∧
      ∀ F : Finset (Finset (Fin n)), is_uncomplemented F →
        ((L * R).submatrix (fun x : F => (x : Finset (Fin n)))
          (fun x : F => (x : Finset (Fin n)))).det ≠ 0)
    (t : ℕ) (𝒜 : Fin t → Finset (Finset (Fin n))) (hunc : ∀ i, is_uncomplemented (𝒜 i))
    (hinc : strongly_incomparable 𝒜) : ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) := by
  obtain ⟨K, _, L, R, hz, hd⟩ := hM
  have h := matrix_block_det_card_sum_le_width L R 𝒜
    (fun i j hij a ha b hb => hz a b (hinc i j hij a ha b hb) (hinc j i (Ne.symm hij) b hb a ha))
    (fun i => hd (𝒜 i) (hunc i))
  simpa using h
