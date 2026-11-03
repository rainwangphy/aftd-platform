import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCostTwo
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.HashProbeTailProbZeroOfLtStrict
import AFTD.Kb.Tcs.HashProbeTailProbZero
import AFTD.Kb.Tcs.HashProbeTailProbOne
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# prime_fixed_offset_tail_prob_two_two

Topic: data_structures   Node: 52b3c785950c

Provenance: helper lemma. step towards prime_fixed_offset_linear_probe_tail_prob_interior_t_two

For any odd prime p and any bijective offset sequence r : Fin p → ZMod p with r 0 = 0, the second tail probability at load t = 2 is exactly 3 / p^2.
-/

/-- For any odd prime p and any bijective offset sequence r : Fin p → ZMod p with r 0 = 0, the second tail probability at load t = 2 is exactly 3 / p^2. -/
theorem prime_fixed_offset_tail_prob_two_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p)
    (r : Fin p → ZMod p) (hr_bij : Function.Bijective r) (hr0 : r 0 = 0) :
    hash_probe_tail_prob p r 2 2 = 3 / (p : ℝ)^2 := by
  have hp_ne : r 1 + r 1 ≠ 0 := by
    intro h
    have h_mul : (2 : ZMod p) * r 1 = 0 := by
      calc (2 : ZMod p) * r 1 = r 1 + r 1 := two_mul (r 1)
      _ = 0 := h
    have hp2 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : (p : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
      have : p ≤ 2 := Nat.le_of_dvd (by decide) this
      omega
    have hr1 : r 1 = 0 := by
      cases mul_eq_zero.mp h_mul with
      | inl h2 => contradiction
      | inr h1 => exact h1
    have h10 : (1 : Fin p) = 0 := hr_bij.injective (hr1.trans hr0.symm)
    have h' : (1 : Fin p).val = (0 : Fin p).val := congr_arg Fin.val h10
    rw [Fin.val_zero, Fin.val_one'] at h'
    have : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  have hec : hash_probe_expected_cost p r 2 =
      1 + 2 / (p : ℝ) + 3 / (p : ℝ)^2 := by
    have h := hash_probe_expected_cost_two p hp r hr_bij hr0
    rw [if_neg hp_ne] at h
    simp only [add_zero] at h
    exact h
  have hsum : hash_probe_expected_cost p r 2 =
      hash_probe_tail_prob p r 2 0 + hash_probe_tail_prob p r 2 1 + hash_probe_tail_prob p r 2 2 := by
    unfold hash_probe_expected_cost
    have hsub : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range (p + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      rcases hx with h | h | h <;> omega
    have hzero : ∀ x ∈ Finset.range (p + 1), x ∉ ({0, 1, 2} : Finset ℕ) →
        hash_probe_tail_prob p r 2 x = 0 := by
      intro x hx hx2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2
      have hx3 : 2 < x := by omega
      exact hash_probe_tail_prob_zero_of_lt_strict p r hr_bij 2 x hp hx3
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  have h0 : hash_probe_tail_prob p r 2 0 = 1 := hash_probe_tail_prob_zero p r 2
  have h1 : hash_probe_tail_prob p r 2 1 = 2 / (p : ℝ) := by
    have hp_ge : 2 ≤ p := by omega
    have ht_le : 2 ≤ p := by omega
    have h := hash_probe_tail_prob_one p hp_ge r hr_bij hr0 2 ht_le
    exact_mod_cast h
  linarith
