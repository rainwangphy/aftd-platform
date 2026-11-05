import AFTD.Prelude

/-!
# is_equal_marginal_lottery

Topic: fair_division   Node: 11238f4494e9

Provenance: formalization of a published result. Source: arXiv:2609.35280

A lottery p over complete allocations of m chores to n agents has equal marginals if every chore g is assigned to every agent i with probability exactly 1/n.
-/

/-- An allocation lottery has equal marginals if every chore is assigned to each agent with probability 1/n. -/
def is_equal_marginal_lottery {m n : ℕ} (p : (Fin m → Fin n) → ℝ) : Prop := ∀ (g : Fin m) (i : Fin n), (∑ σ : Fin m → Fin n, if σ g = i then p σ else 0) = 1 / (n : ℝ)
