import AFTD.Prelude

/-!
# op_2130_centered_path_potential_bound

Topic: online_algorithms   Node: 96a52a540725

Provenance: helper lemma. OP-2130: bound for the centered weighted potential of the path witness

For 2D integers of absolute value below positive D, the sum of the discrepancy at i weighted by 2i+1−2D is at most 2D²(D−1).
-/

private lemma op_2130_centered_bound_aux (D : ℕ) (hD : 1 ≤ D) (d : Fin (D + D) → ℤ)
    (h : ∀ i, |d i| < (D : ℤ)) :
    (∑ i : Fin (D + D), (2 * (i.val : ℤ) + 1 - 2 * (D : ℤ)) * d i) ≤
      2 * (D : ℤ)^2 * ((D : ℤ) - 1) := by
  rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin D, (2 * (D : ℤ) * ((D : ℤ) - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have hdleft := abs_lt.mp (h (Fin.castAdd D i))
      have hdright := abs_lt.mp (h (Fin.natAdd D i))
      have hi : (i.val : ℤ) < (D : ℤ) := by exact_mod_cast i.isLt
      have hi0 : (0 : ℤ) ≤ (i.val : ℤ) := by positivity
      have hp : 0 ≤ 2 * (D : ℤ) - 1 - 2 * (i.val : ℤ) := by omega
      have hq : 0 ≤ 2 * (i.val : ℤ) + 1 := by omega
      have hp' := mul_nonneg hp (show 0 ≤ d (Fin.castAdd D i) + (D : ℤ) - 1 by omega)
      have hq' := mul_nonneg hq (show 0 ≤ (D : ℤ) - 1 - d (Fin.natAdd D i) by omega)
      simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add] at *
      nlinarith
    _ = 2 * (D : ℤ)^2 * ((D : ℤ) - 1) := by simp; ring

theorem op_2130_centered_path_potential_bound (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ) (h : ∀ i, |d i| < (D : ℤ)) : (∑ i : Fin (2 * D), (2 * (i.val : ℤ) + 1 - 2 * (D : ℤ)) * d i) ≤ 2 * (D : ℤ)^2 * ((D : ℤ) - 1) := by
  have hg : ∀ (n : ℕ), n = D + D → ∀ (d : Fin n → ℤ),
      (∀ i, |d i| < (D : ℤ)) →
      (∑ i : Fin n, (2 * (i.val : ℤ) + 1 - 2 * (D : ℤ)) * d i) ≤
        2 * (D : ℤ)^2 * ((D : ℤ) - 1) := by
    intro n hn
    subst n
    exact op_2130_centered_bound_aux D hD
  exact hg (2 * D) (by omega) d h
