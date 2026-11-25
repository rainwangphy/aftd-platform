import AFTD.Prelude
import AFTD.Kb.Tcs.PermSignEqOneOfOddOrder

/-!
# perm_signed_lcm_two_sub_order

Topic: combinatorics   Node: 1f041e9a910f

Provenance: helper lemma. arXiv:2611.29409 Lemma 3.1 proof

For any finite type α and permutation σ of α, the signed difference (sgn(σ) : ℤ) * lcm(2, o(σ)) - (sgn(σ) : ℤ) * o(σ) equals o(σ) if o(σ) is odd, and 0 if o(σ) is even.
-/

/-- Pointwise difference of signed lcm(2, order) and signed order for a permutation. -/
theorem perm_signed_lcm_two_sub_order {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) : (Equiv.Perm.sign σ : ℤ) * (Nat.lcm 2 (orderOf σ) : ℤ) - (Equiv.Perm.sign σ : ℤ) * (orderOf σ : ℤ) = if Odd (orderOf σ) then (orderOf σ : ℤ) else 0 := by
  split_ifs with h
  · have hsign : Equiv.Perm.sign σ = 1 := perm_sign_eq_one_of_odd_order σ h
    have hlcm : Nat.lcm 2 (orderOf σ) = 2 * orderOf σ := by
      rw [Nat.Coprime.lcm_eq_mul]
      rwa [Nat.coprime_two_left]
    rw [hsign, hlcm]
    push_cast
    ring
  · have heven : 2 ∣ orderOf σ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)
    have hlcm : Nat.lcm 2 (orderOf σ) = orderOf σ := Nat.lcm_eq_right heven
    rw [hlcm]
    ring
