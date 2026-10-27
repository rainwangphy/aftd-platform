import AFTD.Prelude
import AFTD.Kb.Tcs.ColoringReversal

/-!
# coloring_reversal_weight_add

Topic: graphs   Node: bdcdb38ba677

Provenance: helper lemma. arXiv:2610.31785 Proposition 3.16 proof

The sum of the weights of a proper coloring kappa and its color reversal coloring_reversal kappa is equal to (n - 1) times the number of vertices.
-/

/-- The sum of the weight of a proper coloring and its reversal equals (n - 1) * |V|. -/
theorem coloring_reversal_weight_add {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (κ : G.Coloring (Fin n)) :
    (∑ v : V, (coloring_reversal κ v : ℕ)) + (∑ v : V, (κ v : ℕ)) =
      (n - 1) * Fintype.card V := by
  rw [← Finset.sum_add_distrib]
  have h (v : V) : (coloring_reversal κ v : ℕ) + (κ v : ℕ) = n - 1 :=
    Nat.sub_add_cancel (Nat.le_pred_of_lt (κ v).isLt)
  simp_rw [h]
  simp [mul_comm]
