import AFTD.Prelude
import AFTD.Kb.Tcs.Op98SqExchangeBound
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.Op98ConflictDegreeBound
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.Weight

/-!
# op_98_eight_approximation

Topic: approximation   Node: 1aaafbfae600

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

Partition the packing O into blocks of at most 4 sets; the factor-2 exchange inequality gives weight(block) ≤ 2·weight(N(A, block)) for each block, and a fixed a ∈ A is counted only for blocks containing a set conflicting with a, of which there are at most |a| ≤ 4. Hence weight(O) ≤ 8·weight(A).
-/

lemma op_98_eight_approximation_step {α : Type*} [DecidableEq α]
    (inst : WeightedSetPackingInstance α 4) (A : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) {x : Finset α} (hx : x ∈ inst.family) :
    inst.weight x ≤ 2 * packing_weight inst (conflict_neighborhood A {x}) := by
  have hp : is_packing inst ({x} : Finset (Finset α)) := by
    constructor
    · intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact hx
    · rw [Finset.coe_singleton]
      exact Set.pairwiseDisjoint_singleton x id
  have hc : ({x} : Finset (Finset α)).card ≤ 4 := by simp
  have h := op_98_sq_exchange_bound inst A {x} hA hp hc
  simpa [packing_weight] using h

lemma op_98_eight_approximation_pw {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (A : Finset (Finset α)) (x : Finset α) :
    packing_weight inst (conflict_neighborhood A {x})
      = ∑ a ∈ A, if ¬ Disjoint a x then inst.weight a else 0 := by
  rw [show conflict_neighborhood A {x} = A.filter (fun a => ¬ Disjoint a x) from by
    ext a; simp [conflict_neighborhood]]
  rw [packing_weight, Finset.sum_filter]

/-- Fallback block-decomposition bound: ratio 8 with the empty repair family. -/
theorem op_98_eight_approximation {α : Type*} [DecidableEq α]
    (inst : WeightedSetPackingInstance α 4) (A O : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hO : is_packing inst O) :
    packing_weight inst O ≤ 8 * packing_weight inst A := by
  have hOsub : O ⊆ inst.family := hO.1
  have hAsub : A ⊆ inst.family := hA.1.1
  have hstep : ∀ x ∈ O, inst.weight x ≤ 2 * packing_weight inst (conflict_neighborhood A {x}) :=
    fun x hx => op_98_eight_approximation_step inst A hA (hOsub hx)
  have h1 : packing_weight inst O
      ≤ 2 * ∑ x ∈ O, packing_weight inst (conflict_neighborhood A {x}) := by
    rw [packing_weight, Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx => hstep x hx
  have h2 : ∑ x ∈ O, packing_weight inst (conflict_neighborhood A {x})
      = ∑ a ∈ A, inst.weight a * ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ) := by
    simp only [op_98_eight_approximation_pw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, mul_comm]
  have h3 : ∑ a ∈ A, inst.weight a * ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ)
      ≤ 4 * packing_weight inst A := by
    have hb : ∀ a ∈ A, inst.weight a * ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ)
        ≤ inst.weight a * 4 := by
      intro a ha
      have hc1 : (O.filter (fun o => ¬ Disjoint a o)).card ≤ a.card :=
        op_98_conflict_degree_bound inst O a hO
      have hc2 : a.card ≤ 4 := inst.card_le a (hAsub ha)
      have hw : (0 : ℚ) ≤ inst.weight a := le_of_lt (inst.weight_pos a (hAsub ha))
      have hc4 : ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ) ≤ 4 := by
        have : (O.filter (fun o => ¬ Disjoint a o)).card ≤ 4 := le_trans hc1 hc2
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_left hc4 hw
    calc ∑ a ∈ A, inst.weight a * ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ)
        ≤ ∑ a ∈ A, inst.weight a * 4 := Finset.sum_le_sum hb
      _ = 4 * packing_weight inst A := by
          rw [packing_weight, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  calc packing_weight inst O
      ≤ 2 * ∑ x ∈ O, packing_weight inst (conflict_neighborhood A {x}) := h1
    _ = 2 * ∑ a ∈ A, inst.weight a * ((O.filter (fun o => ¬ Disjoint a o)).card : ℚ) := by
          rw [h2]
    _ ≤ 2 * (4 * packing_weight inst A) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 8 * packing_weight inst A := by ring
