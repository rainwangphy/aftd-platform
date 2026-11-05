import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SteinParamSet
import AFTD.Kb.GameTheoryEconomics.IsSteinNumber
import AFTD.Kb.GameTheoryEconomics.MuStar
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# stein_param_maps_to

Topic: combinatorial_games   Node: 9496fa0a5550

Provenance: helper lemma. arXiv:2611.05898, Theorem 2.2

The map sending (d, u, v) to d^2 * (u^4 + 4 * v^4) maps each triple in stein_param_set to an integer satisfying is_stein_number.
-/

/-- The parameterization map sends each admissible triple in stein_param_set to an E. P. Stein number. -/
theorem stein_param_maps_to :
    Set.MapsTo (fun (d, u, v) => d^2 * (u^4 + 4 * v^4)) stein_param_set {n | is_stein_number n} := by
  rintro ⟨d, u, v⟩ ⟨hd, hu, hv, hodd, hmu, hle⟩
  dsimp [is_stein_number]
  let m := 2 * d * u * v
  let diff := (u : ℤ)^2 - 2 * (v : ℤ)^2
  let k := (d * diff.natAbs)^2
  let n := d^2 * (u^4 + 4 * v^4)
  have hn_eq : n = m^2 + k := by
    apply (@Nat.cast_inj ℤ).mp
    dsimp [m, k, n]
    push_cast
    simp only [mul_pow, sq_abs]
    dsimp [diff]
    ring
  have hdiff : diff ≠ 0 := by
    intro h
    have h_eq : (u : ℤ)^2 = 2 * (v : ℤ)^2 := by linear_combination h
    have h_odd : Odd ((u : ℤ)^2) := Odd.pow ((Int.odd_coe_nat u).mpr hodd)
    have h_even : Even (2 * (v : ℤ)^2) := even_two_mul _
    rw [h_eq] at h_odd
    rw [← Int.not_even_iff_odd] at h_odd
    exact h_odd h_even
  have hk_pos : 0 < k := by
    have h_abs_pos : 0 < diff.natAbs := Int.natAbs_pos.mpr hdiff
    have h_mul_pos : 0 < d * diff.natAbs := Nat.mul_pos hd h_abs_pos
    dsimp [k]
    exact Nat.pow_pos h_mul_pos
  have hk_le : k ≤ 2 * m := by
    have hd_pos : 0 ≤ (d : ℤ) := by positivity
    have h_mul := mul_le_mul_of_nonneg_left hle hd_pos
    apply (@Nat.cast_le ℤ).mp
    push_cast
    have hk_cast : (k : ℤ) = (d : ℤ) * ((d : ℤ) * diff^2) := by
      dsimp [k]
      push_cast
      simp only [mul_pow, sq_abs]
      ring
    have hm_cast : 2 * (m : ℤ) = (d : ℤ) * (4 * (u : ℤ) * (v : ℤ)) := by
      dsimp [m]
      ring
    rw [hk_cast, hm_cast]
    exact h_mul
  have h_sqrt : n.sqrt = m := by
    rw [hn_eq]
    have h2m : k ≤ m + m := by linarith
    exact Nat.sqrt_add_eq' m h2m
  have hn_pos : 0 < n := by
    rw [hn_eq]
    exact lt_of_lt_of_le hk_pos (Nat.le_add_left k (m^2))
  have hn_sub : n - n.sqrt^2 = k := by
    rw [h_sqrt, hn_eq, Nat.add_sub_cancel_left]
  have hn_add : n + n.sqrt^2 = (d * (u^2 + 2 * v^2))^2 := by
    rw [h_sqrt]
    dsimp [n, m]
    ring
  refine ⟨hn_pos, ?_, ?_, ?_, ?_⟩
  · rw [hn_sub]
    exact hk_pos
  · rw [hn_sub]
    dsimp [k]
    exact IsSquare.sq (d * diff.natAbs)
  · rw [hn_add]
    have h_pos' : 0 < d * (u^2 + 2 * v^2) := by positivity
    exact Nat.pow_pos h_pos'
  · rw [hn_add]
    exact IsSquare.sq (d * (u^2 + 2 * v^2))
