import AFTD.Prelude

/-!
# circulant_row_sum

Topic: combinatorics   Node: 6c714674450c

Provenance: helper lemma. helper for arXiv:2610.27175 Theorem 5 (row sums of the blocks)

Every row of the circulant matrix with first column v sums to the sum of v.
-/

theorem circulant_row_sum {m : ℕ} [NeZero m] (v : Fin m → ℤ) (i : Fin m) :
    ∑ j, Matrix.circulant v i j = ∑ j, v j := by
  simp only [Matrix.circulant_apply]
  exact Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun _ => rfl)
