import AFTD.Prelude

/-!
# op1525_flip_mono_pair_sum

Topic: combinatorics   Node: 3e9bc4142503

Provenance: helper lemma. The monochromatic-pair deck average in the complete pair-part route to OP-1525.

For a finite set of pairs with c marked monochromatic, the sum over all individual-vertex flips of the resulting monochromatic-pair count is (2m−4)c+2m, where m is the number of pairs.
-/

theorem op1525_flip_mono_pair_sum {I : Type*} [Fintype I] (s : I → Bool) :
    let c : ℤ := ∑ i : I, if s i then 1 else 0
    (∑ i : I, 2 * (if s i then c - 1 else c + 1)) =
      (2 * (Fintype.card I : ℤ) - 4) * c + 2 * (Fintype.card I : ℤ) := by
  classical
  let c : ℤ := ∑ i : I, if s i then 1 else 0
  change (∑ i : I, 2 * (if s i then c - 1 else c + 1)) =
    (2 * (Fintype.card I : ℤ) - 4) * c + 2 * (Fintype.card I : ℤ)
  calc
    (∑ i : I, 2 * (if s i then c - 1 else c + 1)) =
        ∑ i : I, (2 * (c + 1) - 4 * (if s i then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : s i <;> simp [h] <;> ring
    _ = (2 * (Fintype.card I : ℤ) - 4) * c + 2 * (Fintype.card I : ℤ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      have hh : (∑ i : I, if s i then (1 : ℤ) else 0) = c := rfl
      rw [hh]
      ring
