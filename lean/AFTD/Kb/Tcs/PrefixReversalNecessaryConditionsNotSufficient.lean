import AFTD.Prelude
import AFTD.Kb.Tcs.PrefixReversal
import AFTD.Kb.Tcs.PrefixReversalSixFiveThreeNotTop

/-!
# prefix_reversal_necessary_conditions_not_sufficient

Topic: combinatorics   Node: f086997bff49

Provenance: formalization of a published result. Source: arXiv:2610.30892 after Lemma 3.2

It is not the case that for all natural numbers 2 ≤ k < m < n satisfying 2 * m > n, at least one of k, m, n even, at least one of k, m, n congruent to 2 or 3 mod 4, gcd(gcd(k, m), n) = 1, m + k ≥ n + 1, and gcd(n - m, n - k) = 1, the three prefix reversals of lengths k, m, n generate the full symmetric group Equiv.Perm (Fin n).
-/

/-- The six necessary conditions for generation by three prefix reversals are not collectively sufficient. -/
theorem prefix_reversal_necessary_conditions_not_sufficient :
    ¬ (∀ (k m n : ℕ),
        2 ≤ k → k < m → m < n →
        2 * m > n →
        (Even k ∨ Even m ∨ Even n) →
        (k % 4 = 2 ∨ k % 4 = 3 ∨ m % 4 = 2 ∨ m % 4 = 3 ∨ n % 4 = 2 ∨ n % 4 = 3) →
        Nat.gcd (Nat.gcd k m) n = 1 →
        m + k ≥ n + 1 →
        Nat.gcd (n - m) (n - k) = 1 →
        Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} = (⊤ : Subgroup (Equiv.Perm (Fin n)))) := by
  intro h
  exact prefix_reversal_six_five_three_not_top
    (h 3 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
