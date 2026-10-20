import AFTD.Prelude
import AFTD.Kb.Tcs.Op98NoSingletonRepair
import AFTD.Kb.Tcs.Op98ConflictDegreeBound
import AFTD.Kb.Tcs.Op98SumConflictNeighborhoodWeight
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.LinearGain

/-!
# op_98_four_approximation

Topic: approximation   Node: e809b50c5c6c

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

Every packing O satisfies packing_weight inst O ≤ 4 * packing_weight inst A under square local optimality with respect to 4-exchanges.
-/

/-- Unconditional factor-4 approximation for 4-set packing under square local optimality, obtained by double counting singleton conflict neighborhoods. -/
theorem op_98_four_approximation {α : Type*} [DecidableEq α] (inst : WeightedSetPackingInstance α 4) (A O : Finset (Finset α)) (hA : is_square_locally_optimal inst 4 A) (hO : is_packing inst O) : packing_weight inst O ≤ 4 * packing_weight inst A := by
  have h1 : packing_weight inst O ≤ ∑ o ∈ O, packing_weight inst (conflict_neighborhood A {o}) := by
    unfold packing_weight
    apply Finset.sum_le_sum
    intro o ho
    have hp : is_packing inst {o} := by
      constructor
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact hO.1 ho
      · simp
    have hc : ({o} : Finset (Finset α)).card = 1 := Finset.card_singleton o
    have hlg := op_98_no_singleton_repair inst A {o} hA hp hc
    unfold linear_gain at hlg
    simp only [packing_weight, Finset.sum_singleton] at hlg
    exact le_of_sub_nonpos hlg
  have h2 := op_98_sum_conflict_neighborhood_weight inst A O
  have h3 : (∑ a ∈ A, inst.weight a * ↑{o ∈ O | ¬Disjoint a o}.card) ≤ 4 * packing_weight inst A := by
    have h_bound : ∀ a ∈ A, inst.weight a * ↑{o ∈ O | ¬Disjoint a o}.card ≤ inst.weight a * 4 := by
      intro a ha
      have ha_fam : a ∈ inst.family := hA.1.1 ha
      have h_w_pos : 0 ≤ inst.weight a := le_of_lt (inst.weight_pos a ha_fam)
      have h_deg := op_98_conflict_degree_bound inst O a hO
      have h_card := inst.card_le a ha_fam
      have h_deg_le_4 : {o ∈ O | ¬Disjoint a o}.card ≤ 4 := le_trans h_deg h_card
      have h_deg_q : (({o ∈ O | ¬Disjoint a o}.card : ℚ) ≤ 4) := by exact_mod_cast h_deg_le_4
      nlinarith
    have h_sum := Finset.sum_le_sum h_bound
    have h_rw : (∑ a ∈ A, inst.weight a * 4) = 4 * packing_weight inst A := by
      unfold packing_weight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    linarith
  linarith
