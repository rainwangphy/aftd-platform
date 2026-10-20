import AFTD.Prelude
import AFTD.Kb.Tcs.Op98SqExchangeBound
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.SquaredWeight

/-!
# op_98_small_packing_bound

Topic: approximation   Node: 29be8b7d395e

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

Special case of the target: when the competing packing has at most 4 sets, weight(O) ≤ 2·weight(A), so c = 2 with the empty repair family suffices.
-/

/-- Small-instance case: ratio 2 with no repairs when the competitor has at most 4 sets. -/
theorem op_98_small_packing_bound {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (A O : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hO : is_packing inst O) (hOc : O.card ≤ 4) :
    packing_weight inst O ≤ 2 * packing_weight inst A := by
  have h1 : packing_weight inst O ≤ 2 * packing_weight inst (conflict_neighborhood A O) :=
    op_98_sq_exchange_bound inst A O hA hO hOc
  have hsub : conflict_neighborhood A O ⊆ A := by
    intro x hx
    simp only [conflict_neighborhood, Finset.mem_filter] at hx
    exact hx.1
  have h2 : packing_weight inst (conflict_neighborhood A O) ≤ packing_weight inst A := by
    rw [packing_weight, packing_weight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x hx _ => le_of_lt (inst.weight_pos x (hA.1.1 hx)))
  linarith
