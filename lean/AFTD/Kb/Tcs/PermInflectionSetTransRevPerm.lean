import AFTD.Prelude
import AFTD.Kb.Tcs.PermInflectionSet
import AFTD.Kb.Tcs.PermSecondDerivativeTransRevPerm
import AFTD.Kb.Tcs.PermSecondDerivative

/-!
# perm_inflection_set_trans_revPerm

Topic: combinatorics   Node: 9f855bf43225

Provenance: helper lemma. arXiv:2610.38237 (Inflection sets of permutations), Example 3.4: the value-reversal symmetry used as its WLOG step

Reversing the values of a permutation σ of Fin n (σ.trans Fin.revPerm) does not change its inflection set: perm_inflection_set (σ.trans Fin.revPerm) = perm_inflection_set σ.
-/

theorem perm_inflection_set_trans_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    perm_inflection_set (σ.trans Fin.revPerm) = perm_inflection_set σ := by
  unfold perm_inflection_set
  simp only [perm_second_derivative_trans_revPerm, neg_mul_neg, neg_eq_zero]
