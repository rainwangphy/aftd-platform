import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_is_midpoint_balanced_of_has_no_unique_sums

Topic: combinatorics   Node: d3692d69fcf8

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Lemma B.1 (first statement: every NUS set in odd characteristic is balanced).

For an odd prime p, every subset of Z/pZ with no unique sums is balanced.
-/

theorem finset_is_midpoint_balanced_of_has_no_unique_sums {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (A : Finset (ZMod p)) (hA : finset_has_no_unique_sums A) : finset_is_midpoint_balanced A := by
  classical
  have hcard := hA.1
  refine ⟨Finset.card_pos.1 (by omega), fun b hb => ?_⟩
  have h2 := hA.2 b hb b hb
  unfold finset_unordered_sum_rep_count at h2
  obtain ⟨z, hz, hzb⟩ := Finset.exists_mem_ne (lt_of_lt_of_le one_lt_two h2) s(b, b)
  rw [Finset.mem_filter] at hz
  induction z using Sym2.ind with
  | h u v =>
    rw [Finset.mk_mem_sym2_iff, Sym2.lift_mk] at hz
    obtain ⟨⟨hu, hv⟩, huv⟩ := hz
    have two_ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
    refine ⟨u, hu, v, hv, ?_, ?_, ?_, huv.symm⟩
    · intro h
      rw [h] at huv
      have hvb := add_left_cancel huv
      exact hzb (by rw [h, hvb])
    · intro h
      rw [h] at huv
      have hub := add_right_cancel huv
      exact hzb (by rw [h, hub])
    · intro h
      rw [h] at huv
      have hvb : v = b := mul_left_cancel₀ two_ne (by rw [two_mul, two_mul]; exact huv)
      exact hzb (by rw [h, hvb])
