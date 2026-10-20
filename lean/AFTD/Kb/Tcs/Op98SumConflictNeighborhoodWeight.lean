import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.PackingWeight

/-!
# op_98_sum_conflict_neighborhood_weight

Topic: approximation   Node: 49048791cb99

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

The sum of conflict neighborhood weights over a packing O equals the weighted sum of conflict degrees in O over A: ∑_{o ∈ O} weight(N(A, {o})) = ∑_{a ∈ A} weight(a) * |{o ∈ O : ¬ Disjoint a o}|.
-/

/-- Double counting identity for conflict neighborhoods: the sum over O of neighborhood weights equals the sum over A of weights times conflict degrees in O. -/
theorem op_98_sum_conflict_neighborhood_weight {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (A O : Finset (Finset α)) :
    ∑ o ∈ O, packing_weight inst (conflict_neighborhood A {o}) =
    ∑ a ∈ A, inst.weight a * (O.filter (fun o => ¬ Disjoint a o)).card := by
  have h1 : (∑ o ∈ O, packing_weight inst (conflict_neighborhood A {o})) =
      ∑ o ∈ O, ∑ a ∈ A, if ¬ Disjoint a o then inst.weight a else 0 := by
    apply Finset.sum_congr rfl
    intro o ho
    simp only [packing_weight, conflict_neighborhood]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    simp
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter, Finset.sum_const]
  simp [nsmul_eq_mul, mul_comm]
