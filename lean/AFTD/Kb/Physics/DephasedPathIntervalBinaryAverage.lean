import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathIntervalPolynomial
import AFTD.Kb.Physics.DephasedPathIntervalBlock
import AFTD.Kb.Physics.DephasedColorCoefficient

/-!
# dephased_path_interval_binary_average

Topic: quantum_mechanics   Node: 9f2f77d322c6

Provenance: helper lemma. Multi-affine expansion in the OP-827 constant-gap certificate route.

The colored interval polynomial at arbitrary real weights equals its weighted average over all zero-one profiles.
-/

open scoped BigOperators
set_option maxHeartbeats 2000000

theorem independent_binary_monomial_average_work {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (X : Finset ι) :
    (∑ f : ι → Bool, ∏ i : ι,
      (if f i then q i else 1 - q i) * (if i ∈ X then (if f i then 1 else 0) else 1)) =
      ∏ i ∈ X, q i := by
  classical
  calc
    _ = ∏ i, ∑ b : Bool, (if b then q i else 1 - q i) *
        (if i ∈ X then (if b then 1 else 0) else 1) :=
      (Fintype.prod_sum (fun i (b : Bool) => (if b then q i else 1 - q i) *
        (if i ∈ X then (if b then 1 else 0) else 1))).symm
    _ = ∏ i, if i ∈ X then q i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Fintype.sum_bool]
      by_cases hiX : i ∈ X <;> simp [hiX] <;> ring
    _ = _ := Fintype.prod_ite_mem X q

open scoped Classical BigOperators in
theorem dephased_path_interval_binary_average (n : ℕ) (color : Fin n → Fin 4) (left right : Finset (Fin 4)) (q : Fin n → ℝ) : (∑ f : Fin n → Bool, (∏ i : Fin n, if f i then q i else 1 - q i) * dephased_path_interval_polynomial n color left right (fun i => if f i then 1 else 0)) = dephased_path_interval_polynomial n color left right q := by
  classical
  unfold dephased_path_interval_polynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i.val ≤ j.val ∧ i.val % 2 = j.val % 2
  · simp only [h, true_and, if_true]
    have hgen (c : ℝ) (X : Finset (Fin n)) :
        (∑ f : Fin n → Bool, (∏ a : Fin n, if f a then q a else 1 - q a) *
          (c * ∏ a ∈ X, if f a then 1 else 0)) = c * ∏ a ∈ X, q a := by
      rw [← independent_binary_monomial_average_work q X, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem]
      ring
    exact hgen _ _

  · simp only [h, false_and, and_false, if_false, mul_zero, Finset.sum_const_zero]
