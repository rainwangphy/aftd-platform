import AFTD.Prelude

/-!
# nonclairvoyant_scheduling_lower_bound

Topic: online_algorithms   Node: a212e588066d

Provenance: formalization of a published result. Source: arXiv:2610.29037 Definition 3.8 and Theorem 3.9

The function `nonclairvoyant_scheduling_lower_bound n lam` is defined as the supremum (sSup) in Real of the set of all real numbers rob for which there exist a natural number alpha and a function p : Nat -> Real satisfying: (1) 1 <= alpha and alpha <= (n^2 + 2 * n) / (3 * n + 1) using natural number division; (2) for every natural number i with 1 <= i <= alpha, i * (2 * n + 1 - i) / 2 + (sum_{j=1}^{i-1} (n - j) * p j) + (n + 1 - i) * (n - i) * p i = rob * (i * (i + 1) / 2 + ((n + i + 1) * (n - i) / 2) * p i) where all integer quantities are cast to Real; (3) lam * n * (n + 1) / 2 = (sum_{j=1}^{alpha - 1} (n - j) * p j) + ((n + 1 - alpha) * (n - alpha) / 2) * p alpha; (4) for all i in {1, ..., alpha}, 0 <= p i and p i <= 1; (5) max (2 * n / (n + 1)) ((n - alpha) / (alpha + 1)) <= rob; and (6) rob <= (n + 1 - alpha) / alpha.
-/

/-- The lower bound Phi^(n)(lambda) on robustness for non-clairvoyant scheduling. -/
noncomputable def nonclairvoyant_scheduling_lower_bound (n : ℕ) (lam : ℝ) : ℝ := sSup { rob : ℝ | ∃ (α : ℕ) (p : ℕ → ℝ),
    1 ≤ α ∧ α ≤ (n^2 + 2 * n) / (3 * n + 1) ∧
    ((∀ i : ℕ, 1 ≤ i → i ≤ α →
      (i : ℝ) * (2 * (n : ℝ) + 1 - (i : ℝ)) / 2 +
      (∑ j ∈ Finset.Icc 1 (i - 1), ((n : ℝ) - (j : ℝ)) * p j) +
      ((n : ℝ) + 1 - (i : ℝ)) * ((n : ℝ) - (i : ℝ)) * p i =
      rob * ((i : ℝ) * ((i : ℝ) + 1) / 2 + ((n : ℝ) + (i : ℝ) + 1) * ((n : ℝ) - (i : ℝ)) / 2 * p i)) ∧
    (lam * (n : ℝ) * ((n : ℝ) + 1) / 2 =
      (∑ j ∈ Finset.Icc 1 (α - 1), ((n : ℝ) - (j : ℝ)) * p j) +
      ((n : ℝ) + 1 - (α : ℝ)) * ((n : ℝ) - (α : ℝ)) / 2 * p α) ∧
    (∀ i ∈ Finset.Icc 1 α, 0 ≤ p i ∧ p i ≤ 1)) ∧
    max (2 * (n : ℝ) / ((n : ℝ) + 1)) (((n : ℝ) - (α : ℝ)) / ((α : ℝ) + 1)) ≤ rob ∧
    rob ≤ ((n : ℝ) + 1 - (α : ℝ)) / (α : ℝ) }
