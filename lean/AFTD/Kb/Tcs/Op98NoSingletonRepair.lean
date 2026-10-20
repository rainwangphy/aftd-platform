import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.IsSquareLocallyOptimal
import AFTD.Kb.Tcs.LinearGain

/-!
# op_98_no_singleton_repair

Topic: approximation   Node: 05de679babc0

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

Under square local optimality a single-set exchange never has positive linear gain: for X = {s}, w(s)² ≤ squared_weight(N(A,{s})) ≤ weight(N(A,{s}))², hence linear_gain inst A {s} ≤ 0.
-/

/-- No single-set exchange has positive linear gain under square local optimality, so every repair has at least 2 sets. -/
theorem op_98_no_singleton_repair {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (A X : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hX : is_packing inst X) (hXc : X.card = 1) :
    linear_gain inst A X ≤ 0 := by
  obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hXc
  have hcard : ({s} : Finset (Finset α)).card ≤ 4 := by simp
  have hsq_opt := hA.2 {s} hX hcard
  dsimp [squared_weight] at hsq_opt
  rw [Finset.sum_singleton] at hsq_opt
  have h_nonneg : ∀ x ∈ conflict_neighborhood A {s}, 0 ≤ inst.weight x := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
    exact le_of_lt (inst.weight_pos x (hA.1.1 hxA))
  have hsq_sum := Finset.sum_sq_le_sq_sum_of_nonneg h_nonneg
  have hle_sq : inst.weight s ^ 2 ≤ (∑ x ∈ conflict_neighborhood A {s}, inst.weight x) ^ 2 :=
    hsq_opt.trans hsq_sum
  have hsum_nonneg : 0 ≤ ∑ x ∈ conflict_neighborhood A {s}, inst.weight x :=
    Finset.sum_nonneg h_nonneg
  have hlin : inst.weight s ≤ ∑ x ∈ conflict_neighborhood A {s}, inst.weight x := by
    nlinarith
  dsimp [linear_gain, packing_weight]
  rw [Finset.sum_singleton]
  linarith
