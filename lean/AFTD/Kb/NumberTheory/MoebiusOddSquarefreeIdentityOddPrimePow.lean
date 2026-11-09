import AFTD.Prelude
import AFTD.Kb.NumberTheory.OddSquarefreeIndicator
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# moebius_odd_squarefree_identity_odd_prime_pow

Topic: elementary_number_theory   Node: a0cbb86d9b22

Provenance: helper lemma. arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Proposition 4.2

For any prime natural number $p$ with $p \neq 2$ and any natural number $a$, the sum of the Möbius function $\mu(k)$ over all divisors $k$ of $p^a$ such that $k^2$ divides $p^a$ and $k$ is odd equals $\mu^*(p^a)$.
-/

open Finset in
/-- The odd square divisor Möbius sum for powers of an odd prime equals the odd square-free indicator. -/
theorem moebius_odd_squarefree_identity_odd_prime_pow (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∑ k ∈ (Nat.divisors (p ^ a)).filter (fun k => k ^ 2 ∣ p ^ a ∧ Odd k), ArithmeticFunction.moebius k) =
      odd_squarefree_indicator (p ^ a) := by
  classical
  set T : Finset ℕ := (Nat.divisors (p ^ a)).filter (fun k => k ^ 2 ∣ p ^ a ∧ Odd k) with hTdef
  set S : Finset ℕ := T.filter (fun k => k = 1 ∨ k = p) with hSdef
  -- Indicator evaluation
  have hind : odd_squarefree_indicator (p ^ a) = if 2 ≤ a then 0 else 1 := by
    have hcond : (∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ^ 2 ∣ p ^ a) ↔ a < 2 := by
      constructor
      · intro h
        by_contra hge
        push Not at hge
        exact h p hp hp2 (pow_dvd_pow p hge)
      · intro ha q hq hq2 hqdvd
        have hq_dvd : q ∣ p ^ a := dvd_trans (dvd_pow_self q (by norm_num)) hqdvd
        have hqp : q ∣ p := hq.dvd_of_dvd_pow hq_dvd
        have hqeqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
        rw [hqeqp] at hqdvd
        have h2 : p ^ 2 ≤ p ^ a := Nat.le_of_dvd (pow_pos hp.pos a) hqdvd
        have ha1 : a ≤ 1 := by omega
        have hle : p ^ a ≤ p := by simpa using Nat.pow_le_pow_right hp.pos ha1
        nlinarith [hp.two_le]
    unfold odd_squarefree_indicator
    rw [if_congr hcond rfl rfl]
    by_cases h : a < 2
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  -- reduce sum over T to sum over S
  have hST : ∑ k ∈ S, ArithmeticFunction.moebius k = ∑ k ∈ T, ArithmeticFunction.moebius k := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [hSdef, Finset.mem_filter] at hx
      exact hx.1
    · intro x hxT hxS
      have hxS' : ¬ (x = 1 ∨ x = p) := by
        intro h
        apply hxS
        rw [hSdef, Finset.mem_filter]
        exact ⟨hxT, h⟩
      have hx1 : x ≠ 1 := fun h => hxS' (Or.inl h)
      have hxp : x ≠ p := fun h => hxS' (Or.inr h)
      rw [hTdef, Finset.mem_filter, Nat.mem_divisors] at hxT
      obtain ⟨⟨hxdvd, -⟩, -⟩ := hxT
      obtain ⟨i, hi, hxi⟩ := (Nat.dvd_prime_pow hp).1 hxdvd
      have hi0 : i ≠ 0 := by rintro rfl; rw [pow_zero] at hxi; exact hx1 hxi
      have hi1 : i ≠ 1 := by rintro rfl; rw [pow_one] at hxi; exact hxp hxi
      have hi2 : 2 ≤ i := by omega
      have hpdvdx : p ^ 2 ∣ x := by rw [hxi]; exact pow_dvd_pow p hi2
      have hnsq : ¬ Squarefree x := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro hsq
        exact hsq p hp (by simpa [pow_two] using hpdvdx)
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
  -- evaluate sum over S
  have hS_le : S ⊆ ({1, p} : Finset ℕ) := by
    intro x hx
    rw [hSdef, Finset.mem_filter] at hx
    obtain ⟨-, hx1p⟩ := hx
    rcases hx1p with rfl | rfl
    · simp
    · simp
  have h1S : (1:ℕ) ∈ S := by
    rw [hSdef, hTdef, Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨⟨one_dvd _, (pow_pos hp.pos a).ne'⟩, ⟨by simp, odd_one⟩⟩, Or.inl rfl⟩
  have hpS : p ∈ S ↔ 2 ≤ a := by
    constructor
    · intro hpS'
      rw [hSdef, hTdef, Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at hpS'
      obtain ⟨⟨⟨-, -⟩, ⟨hpdvd, -⟩⟩, -⟩ := hpS'
      have h2 : p ^ 2 ≤ p ^ a := Nat.le_of_dvd (pow_pos hp.pos a) hpdvd
      by_contra hlt
      have ha1 : a ≤ 1 := by omega
      have hle : p ^ a ≤ p := by simpa using Nat.pow_le_pow_right hp.pos ha1
      nlinarith [hp.two_le]
    · intro h2a
      rw [hSdef, hTdef, Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨⟨dvd_pow_self p (by omega), (pow_pos hp.pos a).ne'⟩, ⟨pow_dvd_pow p h2a, hp.odd_of_ne_two hp2⟩⟩, Or.inr rfl⟩
  have hsum_S : ∑ x ∈ S, ArithmeticFunction.moebius x = (if 2 ≤ a then 0 else 1) := by
    have hcongr : ∑ x ∈ S, ArithmeticFunction.moebius x = ∑ x ∈ S, (if x ∈ S then ArithmeticFunction.moebius x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos hx]
    have hsub := Finset.sum_subset (s₁ := S) (s₂ := ({1,p} : Finset ℕ)) hS_le
      (f := fun x => if x ∈ S then ArithmeticFunction.moebius x else 0)
      (by intro x hx hxS; simp [hxS])
    have hpair : ∑ x ∈ ({1,p} : Finset ℕ), (if x ∈ S then ArithmeticFunction.moebius x else 0)
        = (if 1 ∈ S then ArithmeticFunction.moebius 1 else 0) + (if p ∈ S then ArithmeticFunction.moebius p else 0) := by
      rw [Finset.sum_pair (Ne.symm hp.ne_one)]
    rw [hcongr, hsub, hpair]
    rw [if_pos h1S, ArithmeticFunction.moebius_apply_one]
    by_cases h : 2 ≤ a
    · rw [if_pos (hpS.mpr h), ArithmeticFunction.moebius_apply_prime hp, if_pos h]
      ring
    · rw [if_neg (fun hc => h (hpS.mp hc)), if_neg h]
      ring
  rw [← hST, hsum_S, hind]
