import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130CoinProjectionFiberCard

/-!
# op2130_coin_projection_mean

Topic: online_algorithms   Node: 5f752ea84072

Provenance: helper lemma. OP-2130, uniform coin projection

The uniform mean of any function of m distinct selected bits of a T-bit tape equals its uniform mean over m-bit tapes.
-/

theorem op2130_coin_projection_sum (T m : ℕ) (hm : m ≤ T) (idx : Fin m → Fin T)
    (hinj : Function.Injective idx) (g : (Fin m → Bool) → ℝ) :
    (∑ r : Fin T → Bool, g (fun j => r (idx j))) =
      (2:ℝ)^(T-m) * ∑ a : Fin m → Bool, g a := by
  classical
  let proj : (Fin T → Bool) → (Fin m → Bool) := fun r j => r (idx j)
  have hF (a : Fin m → Bool) :
      (Finset.univ.filter fun r : Fin T → Bool => proj r = a) =
      (Finset.univ.filter fun r : Fin T → Bool => ∀ j, r (idx j) = a j) := by
    ext r
    simp [proj, funext_iff]
  calc
    (∑ r : Fin T → Bool, g (fun j => r (idx j))) =
      ∑ a : Fin m → Bool, ∑ r ∈ Finset.univ with proj r = a, g (proj r) := by
        exact (Finset.sum_fiberwise Finset.univ proj (fun r => g (proj r))).symm
    _ = ∑ a : Fin m → Bool, (2:ℝ)^(T-m) * g a := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ r ∈ Finset.univ with proj r = a, g (proj r)) =
            ∑ _r ∈ Finset.univ with proj _r = a, g a := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [(Finset.mem_filter.mp hr).2]
        _ = (2:ℝ)^(T-m) * g a := by
          rw [Finset.sum_const,hF,op2130_coin_projection_fiber_card T m hm idx hinj a]
          simp [nsmul_eq_mul]
    _ = _ := by rw [Finset.mul_sum]

theorem op2130_coin_projection_mean (T m : ℕ) (hm : m ≤ T) (idx : Fin m → Fin T)
    (hinj : Function.Injective idx) (g : (Fin m → Bool) → ℝ) :
    (∑ r : Fin T → Bool, g (fun j => r (idx j))) / (2:ℝ)^T =
      (∑ a : Fin m → Bool, g a) / (2:ℝ)^m := by
  rw [op2130_coin_projection_sum T m hm idx hinj g]
  have hpT : (2:ℝ)^T = (2:ℝ)^(T-m) * (2:ℝ)^m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpT]
  have hp : (2:ℝ)^(T-m) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
