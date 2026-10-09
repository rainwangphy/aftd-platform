import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# consecutive_sum_ne_mul_prime_of_two_mul_lt

Topic: combinatorics   Node: c23141c6cd66

Provenance: original. Related work: arXiv:2610.08889 (Consecutive Cycle Sums), Lemma 2, which assumes in addition 2an − T_{2a−1} < ap; that hypothesis is not needed: divisibility forces a run of k consecutive integers with sum ap to have k ≤ 2a, and such a run sums to at most 2an < ap. Serves Theorem 1 (not_cycle_labeling_complete_range_of_ge_eight).

If p is a prime with p > 2n and a ≥ 1, then a·p is not a sum of one or more consecutive integers from {1, …, n}.
-/

theorem consecutive_sum_ne_mul_prime_of_two_mul_lt (n a p i j : ℕ) (hp : p.Prime)
    (hpn : 2 * n < p) (ha : 0 < a) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    ∑ x ∈ Finset.Icc i j, x ≠ a * p := by
  intro hS
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  -- `2 S = k (2i + k - 1)` with `k = m + 1` terms
  have hsum : ∀ m : ℕ, 2 * ∑ x ∈ Finset.Icc i (i + m), x = (m + 1) * (2 * i + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show i + (m + 1) = (i + m) + 1 by ring, Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  have h2 := hsum m
  rw [hS] at h2
  have hsize : ∑ x ∈ Finset.Icc i (i + m), x ≤ (m + 1) * n := by
    have := Finset.sum_le_card_nsmul (Finset.Icc i (i + m)) (fun x => x) n
      (fun x hx => le_trans (Finset.mem_Icc.1 hx).2 hjn)
    rw [Nat.card_Icc, smul_eq_mul] at this
    rwa [show i + m + 1 - i = m + 1 by omega] at this
  rw [hS] at hsize
  have hkn : m + 1 ≤ n := by omega
  -- a positive number below `p` is coprime to `p`
  have hcop : ∀ t, 0 < t → t ≤ n → Nat.Coprime t p := by
    intro t ht htn
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd ht h) (by omega))
  -- the number of terms is at most `2a`
  have hk : m + 1 ≤ 2 * a := by
    rcases Nat.even_or_odd (m + 1) with ⟨t, ht⟩ | hodd
    · have hS' : a * p = t * (2 * i + m) := by
        have : 2 * (a * p) = 2 * (t * (2 * i + m)) := by rw [h2, ht]; ring
        omega
      have ht0 : 0 < t := by omega
      have htd : t ∣ a := (hcop t ht0 (by omega)).dvd_of_dvd_mul_right ⟨_, hS'⟩
      have := Nat.le_of_dvd ha htd
      omega
    · have hdvd : m + 1 ∣ 2 * (a * p) := ⟨2 * i + m, h2⟩
      have hc2 : Nat.Coprime (m + 1) 2 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
          (Nat.odd_iff.1 hodd ▸ by omega))
      have h1 : m + 1 ∣ a * p := hc2.dvd_of_dvd_mul_left hdvd
      have h3 : m + 1 ∣ a := (hcop (m + 1) (by omega) hkn).dvd_of_dvd_mul_right h1
      have := Nat.le_of_dvd ha h3
      omega
  -- then the sum is at most `2an < ap`
  have : (m + 1) * n ≤ 2 * a * n := Nat.mul_le_mul_right n hk
  have : 2 * a * n < a * p := by nlinarith
  omega
