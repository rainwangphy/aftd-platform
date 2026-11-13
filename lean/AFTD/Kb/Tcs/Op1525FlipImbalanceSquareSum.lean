import AFTD.Prelude

/-!
# op1525_flip_imbalance_square_sum

Topic: combinatorics   Node: ad1f30052ed4

Provenance: helper lemma. A switching-deck imbalance identity for OP-1525 and arXiv:2611.13901, Section 4.1.

For signs on a finite set, the sum over vertices of the squared total sign after flipping that vertex is (n−4) times the original squared total sign plus 4n.
-/

theorem op1525_flip_imbalance_square_sum {V : Type*} [Fintype V]
    (f : V → ℤ) (h : ∀ v, f v = 1 ∨ f v = -1) :
    (∑ v : V, ((∑ u : V, f u) - 2 * f v)^2) =
      ((Fintype.card V : ℤ) - 4) * (∑ u : V, f u)^2 +
        4 * (Fintype.card V : ℤ) := by
  classical
  let S : ℤ := ∑ u : V, f u
  have hf (v : V) : f v ^ 2 = 1 := by
    rcases h v with hv | hv <;> rw [hv] <;> norm_num
  change (∑ v : V, (S - 2 * f v)^2) =
    ((Fintype.card V : ℤ) - 4) * S^2 + 4 * (Fintype.card V : ℤ)
  calc
    (∑ v : V, (S - 2 * f v)^2) = ∑ v : V, (S^2 - 4 * S * f v + 4) := by
      apply Finset.sum_congr rfl
      intro v _
      calc
        (S - 2 * f v)^2 = S^2 - 4 * S * f v + 4 * f v^2 := by ring
        _ = S^2 - 4 * S * f v + 4 := by rw [hf]; ring
    _ = ((Fintype.card V : ℤ) - 4) * S^2 + 4 * (Fintype.card V : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      have hh : (∑ v : V, f v) = S := rfl
      rw [hh]
      ring
