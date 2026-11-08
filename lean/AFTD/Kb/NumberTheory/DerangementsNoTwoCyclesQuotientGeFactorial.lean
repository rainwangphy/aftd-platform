import AFTD.Prelude
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesQuotient
import AFTD.Kb.NumberTheory.DerangementsNoTwoCyclesCount

/-!
# derangements_no_two_cycles_quotient_ge_factorial

Topic: elementary_number_theory   Node: 6f126e62845e

Provenance: formalization of a published result. Source: scout/2610-40342-a-p-adic-valuation-calculus-for-permutations-with-restricte.md:1633

For every natural number n ≥ 3, the quotient derangements_no_two_cycles_quotient n is at least (n - 3)!.
-/

/-- Factorial lower bound on the quotient: Q_n ≥ (n - 3)! for n ≥ 3. -/
theorem derangements_no_two_cycles_quotient_ge_factorial (n : ℕ) (hn : 3 ≤ n) : (n - 3).factorial ≤ derangements_no_two_cycles_quotient n := by
  have hn2 : 2 ≤ n := le_trans (by decide) hn
  have h_card := Equiv.Perm.card_of_cycleType_singleton (α := Fin n) (n := n) hn2 (by simp)
  simp only [Fintype.card_fin, Nat.choose_self, mul_one] at h_card
  have h_sub : ({g : Equiv.Perm (Fin n) | g.cycleType = {n}} : Finset (Equiv.Perm (Fin n))) ⊆
      ({σ : Equiv.Perm (Fin n) | ∀ (x : Fin n),
        ({y : Fin n | σ.SameCycle x y} : Finset (Fin n)).card ∉ (({1, 2} : Finset ℕ) : Set ℕ)} : Finset (Equiv.Perm (Fin n))) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    have hcyc : σ.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hσ]
      rfl
    have hsupp : σ.support.card = n := by
      rw [← Equiv.Perm.sum_cycleType, hσ]
      rfl
    have hsupp_univ : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hsupp, Fintype.card_fin]
    intro x
    have hx : x ∈ σ.support := by rw [hsupp_univ]; exact Finset.mem_univ x
    have h_same : ∀ y : Fin n, σ.SameCycle x y := by
      intro y
      have hy : y ∈ σ.support := by rw [hsupp_univ]; exact Finset.mem_univ y
      rw [Equiv.Perm.mem_support] at hx hy
      exact hcyc.sameCycle hx hy
    have h_filt : ({y : Fin n | σ.SameCycle x y} : Finset (Fin n)) = Finset.univ := by
      ext y
      simp [h_same y]
    rw [h_filt, Finset.card_univ, Fintype.card_fin]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have h_le := Finset.card_le_card h_sub
  rw [h_card] at h_le
  change (n - 1).factorial ≤ derangements_no_two_cycles_count n at h_le
  have h_fact : (n - 1).factorial = (n - 1) * (n - 2) * (n - 3).factorial := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h1 : 3 + k - 1 = k + 2 := by omega
    have h2 : 3 + k - 2 = k + 1 := by omega
    have h3 : 3 + k - 3 = k := by omega
    rw [h1, h2, h3]
    rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    ring
  rw [h_fact] at h_le
  have h_pos : 0 < (n - 1) * (n - 2) := by
    have : 0 < n - 1 := by omega
    have : 0 < n - 2 := by omega
    positivity
  dsimp [derangements_no_two_cycles_quotient]
  rw [Nat.le_div_iff_mul_le h_pos]
  rw [mul_comm]
  exact h_le
