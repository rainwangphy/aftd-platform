import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative
import AFTD.Kb.Tcs.HasDegreeLe

/-!
# boolean_derivative_has_degree_le_pred

Topic: cryptography   Node: dec562a3cf4b

Provenance: helper lemma. step towards boolean_derivative_bent_dim_eight_degree_le

The directional derivative of any Boolean function of algebraic degree at most d + 1 along any vector v has algebraic degree at most d.
-/

lemma boolean_derivative_has_degree_le_pred_zmod2_mul_eq_ite (c : ZMod 2) (m : ZMod 2) :
    c * m = if c = 1 then m else 0 := by
  by_cases h : c = 1
  · rw [h, if_pos rfl, one_mul]
  · rw [if_neg h]
    have : c = 0 := by
      revert c h
      decide
    rw [this, zero_mul]

lemma boolean_derivative_has_degree_le_pred_prod_add_cancel {n : ℕ} (S : Finset (Fin n)) (x v : Fin n → ZMod 2) :
    (∏ i ∈ S, x i) + (∏ i ∈ S, (x i + v i)) =
    ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, v i) * (∏ i ∈ T, x i) := by
  have hp := Finset.prod_add x v S
  rw [hp]
  have hmem : S ∈ S.powerset := Finset.mem_powerset_self S
  rw [← Finset.add_sum_erase S.powerset _ hmem]
  have hS : (∏ i ∈ S, x i) * ∏ i ∈ S \ S, v i = ∏ i ∈ S, x i := by
    rw [Finset.sdiff_self, Finset.prod_empty, mul_one]
  rw [hS, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [mul_comm]

/-- The directional derivative of any Boolean function of algebraic degree at most d + 1 along any vector has algebraic degree at most d. -/
theorem boolean_derivative_has_degree_le_pred {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (v : Fin n → ZMod 2) {d : ℕ} (hf : has_degree_le f (d + 1)) : has_degree_le (boolean_derivative v f) d := by
  rcases hf with ⟨c, hc_card, hc_sum⟩
  let coeff : Finset (Fin n) → ZMod 2 := fun T =>
    ∑ S ∈ c, if T ∈ S.powerset.erase S then (∏ i ∈ S \ T, v i) else 0
  let c' : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun T => coeff T = 1)
  use c'
  constructor
  · intro T hT
    rw [Finset.mem_filter] at hT
    have hT_coeff : coeff T = 1 := hT.2
    have hT_ne_zero : coeff T ≠ 0 := by
      rw [hT_coeff]
      decide
    by_contra h_not
    have h_not_in : ∀ S ∈ c, T ∉ S.powerset.erase S := by
      intro S hS h_in
      have h_card_S := hc_card S hS
      rw [Finset.mem_erase, Finset.mem_powerset] at h_in
      have h_ssubset : T ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        exact ⟨h_in.2, h_in.1⟩
      have h_card_lt := Finset.card_lt_card h_ssubset
      omega
    have h_zero : coeff T = 0 := by
      dsimp [coeff]
      apply Finset.sum_eq_zero
      intro S hS
      rw [if_neg (h_not_in S hS)]
    exact hT_ne_zero h_zero
  · intro x
    dsimp [boolean_derivative]
    rw [hc_sum x, hc_sum (x + v)]
    have h_sum_add : (∑ S ∈ c, ∏ i ∈ S, x i) + (∑ S ∈ c, ∏ i ∈ S, (x + v) i) =
        ∑ S ∈ c, ((∏ i ∈ S, x i) + ∏ i ∈ S, (x i + v i)) := by
      change (∑ S ∈ c, ∏ i ∈ S, x i) + (∑ S ∈ c, ∏ i ∈ S, (x i + v i)) = _
      rw [Finset.sum_add_distrib.symm]
    rw [h_sum_add]
    have h_step1 : (∑ S ∈ c, ((∏ i ∈ S, x i) + ∏ i ∈ S, (x i + v i))) =
        ∑ S ∈ c, ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, v i) * (∏ i ∈ T, x i) := by
      apply Finset.sum_congr rfl
      intro S _
      exact boolean_derivative_has_degree_le_pred_prod_add_cancel S x v
    rw [h_step1]
    have h_step2 : (∑ S ∈ c, ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, v i) * (∏ i ∈ T, x i)) =
        ∑ S ∈ c, ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))),
          (if T ∈ S.powerset.erase S then (∏ i ∈ S \ T, v i) else 0) * (∏ i ∈ T, x i) := by
      apply Finset.sum_congr rfl
      intro S _
      have h_univ : (∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, v i) * (∏ i ∈ T, x i)) =
          ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))),
            if T ∈ S.powerset.erase S then (∏ i ∈ S \ T, v i) * (∏ i ∈ T, x i) else 0 := by
        conv_lhs => rw [← Finset.univ_inter (S.powerset.erase S)]
        exact (Finset.sum_ite_mem Finset.univ (S.powerset.erase S) _).symm
      rw [h_univ]
      apply Finset.sum_congr rfl
      intro T _
      split_ifs with h
      · rfl
      · rw [zero_mul]
    rw [h_step2]
    rw [Finset.sum_comm]
    have h_step3 : (∑ T ∈ (Finset.univ : Finset (Finset (Fin n))),
          ∑ S ∈ c, (if T ∈ S.powerset.erase S then (∏ i ∈ S \ T, v i) else 0) * (∏ i ∈ T, x i)) =
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))), coeff T * (∏ i ∈ T, x i) := by
      apply Finset.sum_congr rfl
      intro T _
      dsimp [coeff]
      rw [← Finset.sum_mul]
    rw [h_step3]
    have h_step4 : (∑ T ∈ (Finset.univ : Finset (Finset (Fin n))), coeff T * (∏ i ∈ T, x i)) =
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))), if coeff T = 1 then (∏ i ∈ T, x i) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      exact boolean_derivative_has_degree_le_pred_zmod2_mul_eq_ite (coeff T) (∏ i ∈ T, x i)
    rw [h_step4]
    exact (Finset.sum_filter (fun T => coeff T = 1) (fun T => ∏ i ∈ T, x i)).symm
