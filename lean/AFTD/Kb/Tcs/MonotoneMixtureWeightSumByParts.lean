import AFTD.Prelude
import AFTD.Kb.Tcs.MonotoneMixtureWeight
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# monotoneMixtureWeight_sum_by_parts

Topic: information   Node: e29b9d2942d9

Provenance: helper lemma. arXiv:2610.01563 Lemma 3 (1) proof

For any sequence $P : \mathbb{N}^+ \to \mathbb{R}$ and any $n \in \mathbb{N}^+, the finite sum of mixture weights satisfies $\sum_{k=1}^n w_k = \sum_{k=1}^n P(k) - n P(n+1)$.
-/

/-- Summation by parts for finite sums of mixture weights. -/
lemma monotoneMixtureWeight_sum_by_parts (P : ℕ+ → ℝ) (n : ℕ+) :
    ∑ k ∈ Finset.Iic n, monotoneMixtureWeight P k =
      (∑ k ∈ Finset.Iic n, P k) - (n : ℝ) * P (n + 1) := by
  induction n using PNat.recOn with
  | one =>
    have h1 : Finset.Iic (1 : ℕ+) = {1} := by
      have : (1 : ℕ+) = ⊥ := rfl
      rw [this, Finset.Iic_bot]
    rw [h1, Finset.sum_singleton, Finset.sum_singleton]
    unfold monotoneMixtureWeight
    push_cast
    ring
  | succ n ih =>
    rw [Finset.sum_Iic_add_zero, Finset.sum_Iic_add_zero, ih]
    unfold monotoneMixtureWeight
    push_cast
    ring
