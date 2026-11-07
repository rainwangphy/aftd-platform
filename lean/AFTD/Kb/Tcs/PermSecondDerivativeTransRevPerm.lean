import AFTD.Prelude
import AFTD.Kb.Tcs.PermSecondDerivative

/-!
# perm_second_derivative_trans_revPerm

Topic: combinatorics   Node: b4958871ec29

Provenance: helper lemma. arXiv:2610.38237 (Inflection sets of permutations), Example 3.4: the value-reversal symmetry used as its WLOG step

Reversing the values of a permutation σ of Fin n (composing with Fin.revPerm, v ↦ n-1-v) negates its discrete second derivative at every ℓ: perm_second_derivative (σ.trans Fin.revPerm) ℓ = - perm_second_derivative σ ℓ.
-/

theorem perm_second_derivative_trans_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) :
    perm_second_derivative (σ.trans Fin.revPerm) ℓ = - perm_second_derivative σ ℓ := by
  unfold perm_second_derivative
  split_ifs with h
  · simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev]
    have h1 := (σ ⟨ℓ, by omega⟩).isLt
    have h2 := (σ ⟨ℓ - 2, by omega⟩).isLt
    have h3 := (σ ⟨ℓ - 1, by omega⟩).isLt
    push_cast [Nat.cast_sub (by omega : (σ ⟨ℓ, by omega⟩ : ℕ) + 1 ≤ n),
      Nat.cast_sub (by omega : (σ ⟨ℓ - 2, by omega⟩ : ℕ) + 1 ≤ n),
      Nat.cast_sub (by omega : (σ ⟨ℓ - 1, by omega⟩ : ℕ) + 1 ≤ n)]
    ring
  · simp
