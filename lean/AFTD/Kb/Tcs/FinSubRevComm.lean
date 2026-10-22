import AFTD.Prelude

/-!
# fin_sub_rev_comm

Topic: combinatorics   Node: c4196d6186b5

Provenance: helper lemma. helper for X R = R Xᵀ for circulant X, arXiv:2610.27175 Theorem 3/5

In Fin m (m > 0), i - (m - 1 - j) = j - (m - 1 - i), both being i + j + 1 mod m.
-/

theorem fin_sub_rev_comm {m : ℕ} [NeZero m] (i j : Fin m) : i - j.rev = j - i.rev := by
  rw [Fin.ext_iff, Fin.sub_def, Fin.sub_def]
  simp only [Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  have h1 : m - (m - (j + 1)) + i = m - (m - (i + 1)) + j := by omega
  rw [h1]
