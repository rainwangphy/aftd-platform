import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialMatrix
import AFTD.Kb.Tcs.PetrialCoeff

/-!
# petrial_nullity_poly_coeff_eq_petrial_coeff

Topic: combinatorics   Node: 62c4fef0423e

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

For every finite graph G on V and every k ≤ |V|, the coefficient of w^(|V| - k) in the nullity generating polynomial equals petrial_coeff G k (the number of vertex subsets F whose partial Petrial matrix has rank k).
-/

/-- For k ≤ |V| the coefficient of w^(|V|-k) in the nullity polynomial is petrial_coeff G k. -/
theorem petrial_nullity_poly_coeff_eq_petrial_coeff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : k ≤ Fintype.card V) :
    (petrial_nullity_poly G).coeff (Fintype.card V - k) = petrial_coeff G k := by
  classical
  unfold petrial_nullity_poly petrial_coeff
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  apply congrArg Finset.card
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hle := (petrial_matrix G F).rank_le_card_width
  omega
