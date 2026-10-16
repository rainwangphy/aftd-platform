import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.PowerDivergenceGenerator

/-!
# mutual_power_divergence_information_eq_sum_rpow

Topic: information   Node: 428ad55e3d49

Provenance: helper lemma. Lemma for mutual_power_divergence_information_subadditive_of_two_thirds_le; standard closed form of power divergences, arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. I.

For β ∈ (0, 1) and a joint probability mass function p_{XY}, the mutual f_β-information equals (Σ_{x,y} p(x, y)^β (p_X(x) p_Y(y))^{1−β} − 1)/(β(β − 1)).
-/

theorem mutual_power_divergence_information_eq_sum_rpow {X Y : Type*} [Fintype X] [Fintype Y]
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (p : X → Y → ℝ) (hp : ∀ x y, 0 ≤ p x y)
    (hp1 : ∑ x, ∑ y, p x y = 1) :
    mutual_f_information (power_divergence_generator β) p =
      (∑ x, ∑ y, p x y ^ β * ((∑ y', p x y') * (∑ x', p x' y)) ^ (1 - β) - 1) / (β * (β - 1)) := by
  have _ := hβ1
  have h_term : ∀ (x : X) (y : Y),
      ((∑ y', p x y') * ∑ x', p x' y) * power_divergence_generator β (p x y / ((∑ y', p x y') * ∑ x', p x' y)) =
        (p x y ^ β * ((∑ y', p x y') * ∑ x', p x' y) ^ (1 - β) - β * p x y + (β - 1) * ((∑ y', p x y') * ∑ x', p x' y)) / (β * (β - 1)) := by
    intro x y
    set q := (∑ y', p x y') * ∑ x', p x' y
    change q * (((p x y / q) ^ β - β * (p x y / q) + (β - 1)) / (β * (β - 1))) = _
    rw [← mul_div_assoc]
    congr 1
    have hq_nonneg : 0 ≤ q := by
      apply mul_nonneg
      · exact Finset.sum_nonneg (fun y' _ => hp x y')
      · exact Finset.sum_nonneg (fun x' _ => hp x' y)
    rcases eq_or_lt_of_le hq_nonneg with hq_zero | hq_pos
    · have hq0 : q = 0 := hq_zero.symm
      have hp_zero : p x y = 0 := by
        cases mul_eq_zero.mp hq0 with
        | inl hx =>
          have hx_all : ∀ y', p x y' = 0 := by
            rw [Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => hp x y')] at hx
            exact fun y' => hx y' (Finset.mem_univ y')
          exact hx_all y
        | inr hy =>
          have hy_all : ∀ x', p x' y = 0 := by
            rw [Finset.sum_eq_zero_iff_of_nonneg (fun x' _ => hp x' y)] at hy
            exact fun x' => hy x' (Finset.mem_univ x')
          exact hy_all x
      rw [hq0, hp_zero]
      rw [zero_mul, Real.zero_rpow (ne_of_gt hβ0)]
      ring
    · have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      rw [Real.div_rpow (hp x y) (le_of_lt hq_pos)]
      have hq_pow : q ^ (1 - β) = q / q ^ β := by
        rw [Real.rpow_sub hq_pos, Real.rpow_one]
      rw [hq_pow]
      have h1 : q * (p x y ^ β / q ^ β) = p x y ^ β * (q / q ^ β) := by ring
      have h2 : q * (β * (p x y / q)) = β * p x y := by
        calc q * (β * (p x y / q)) = β * (q * (p x y / q)) := by ring
        _ = β * p x y := by rw [mul_div_cancel₀ (p x y) hq_ne]
      calc q * (p x y ^ β / q ^ β - β * (p x y / q) + (β - 1))
        _ = q * (p x y ^ β / q ^ β) - q * (β * (p x y / q)) + (β - 1) * q := by ring
        _ = p x y ^ β * (q / q ^ β) - β * p x y + (β - 1) * q := by rw [h1, h2]
  unfold mutual_f_information
  simp_rw [h_term]
  simp_rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h_beta : ∑ x, ∑ y, β * p x y = β := by
    have h : (∑ x, ∑ y, β * p x y) = β * ∑ x, ∑ y, p x y := by simp_rw [← Finset.mul_sum]
    rw [h, hp1, mul_one]
  have hq : ∑ x, ∑ y, ((∑ y', p x y') * ∑ x', p x' y) = 1 := by
    have h_inner : ∀ x, ∑ y, ((∑ y', p x y') * ∑ x', p x' y) = ∑ y', p x y' := by
      intro x
      rw [← Finset.mul_sum]
      have h_comm : ∑ y, ∑ x', p x' y = ∑ x', ∑ y, p x' y := Finset.sum_comm
      rw [h_comm, hp1, mul_one]
    calc ∑ x, ∑ y, ((∑ y', p x y') * ∑ x', p x' y)
      _ = ∑ x, ∑ y', p x y' := by simp_rw [h_inner]
      _ = 1 := hp1
  have h_q_term : ∑ x, ∑ y, (β - 1) * ((∑ y', p x y') * ∑ x', p x' y) = β - 1 := by
    have h : (∑ x, ∑ y, (β - 1) * ((∑ y', p x y') * ∑ x', p x' y)) =
        (β - 1) * ∑ x, ∑ y, ((∑ y', p x y') * ∑ x', p x' y) := by simp_rw [← Finset.mul_sum]
    rw [h, hq, mul_one]
  rw [h_beta, h_q_term]
  ring
