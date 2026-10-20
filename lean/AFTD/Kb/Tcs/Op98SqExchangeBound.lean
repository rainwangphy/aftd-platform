import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# op_98_sq_exchange_bound

Topic: approximation   Node: 9a7f02f5f4d2

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

Objective switching, first half: square local optimality turns the squared potential inequality for exchanges of at most 4 sets into a factor-2 linear exchange inequality, weight(X) ≤ 2·weight(N(A,X)).
-/

/-- Factor-2 linear exchange inequality following from square local optimality of 4-exchanges. -/
theorem op_98_sq_exchange_bound {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (A X : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hX : is_packing inst X) (hXc : X.card ≤ 4) :
    packing_weight inst X ≤ 2 * packing_weight inst (conflict_neighborhood A X) := by
  obtain ⟨hAp, hloc⟩ := hA
  set N := conflict_neighborhood A X with hN
  have hNsub : N ⊆ inst.family := by
    intro a ha
    simp only [hN, conflict_neighborhood, Finset.mem_filter] at ha
    exact hAp.1 ha.1
  have hwN : ∀ s ∈ N, 0 ≤ inst.weight s := fun s hs => le_of_lt (inst.weight_pos s (hNsub hs))
  have hwX : ∀ s ∈ X, 0 ≤ inst.weight s := fun s hs => le_of_lt (inst.weight_pos s (hX.1 hs))
  have h1 : (packing_weight inst X) ^ 2 ≤ (X.card : ℚ) * squared_weight inst X := by
    rw [packing_weight, squared_weight]
    exact sq_sum_le_card_mul_sum_sq
  have h2 : squared_weight inst X ≤ squared_weight inst N := hloc X hX hXc
  have h3 : squared_weight inst N ≤ (packing_weight inst N) ^ 2 := by
    rw [squared_weight, packing_weight]
    exact Finset.sum_sq_le_sq_sum_of_nonneg hwN
  have h4 : (X.card : ℚ) ≤ 4 := by exact_mod_cast hXc
  have hw : 0 ≤ packing_weight inst X := Finset.sum_nonneg hwX
  have hv : 0 ≤ packing_weight inst N := Finset.sum_nonneg hwN
  have hmain : (packing_weight inst X) ^ 2 ≤ (2 * packing_weight inst N) ^ 2 := by nlinarith
  have habs : |packing_weight inst X| ≤ |2 * packing_weight inst N| := sq_le_sq.mp hmain
  rw [abs_of_nonneg hw,
    abs_of_nonneg (by linarith : (0 : ℚ) ≤ 2 * packing_weight inst N)] at habs
  linarith
