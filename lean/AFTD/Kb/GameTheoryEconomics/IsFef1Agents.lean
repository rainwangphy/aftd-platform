import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fef1_agents

Topic: fair_division   Node: 6c4692a9d55c

Provenance: formalization of a published result. Source: arXiv:2611.34488 Def. 2.1

Given common item sizes s : Fin m → ℝ, individual agent budgets B : Fin n → ℝ, and additive valuations given by item values v : Fin n → Fin m → ℝ, an allocation A : Fin n → Finset (Fin m) satisfies FEF1 between agents if for every pair of distinct agents i ≠ j in Fin n and every nonempty subset T ⊆ A j with total size additive_valuation s T ≤ B i, there exists a good g ∈ T such that additive_valuation (v i) (T.erase g) ≤ additive_valuation (v i) (A i).
-/

/-- FEF1 between agents under common item sizes and individual budgets. -/
def is_fef1_agents {m n : ℕ} (s : Fin m → ℝ) (B : Fin n → ℝ)
    (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ T : Finset (Fin m), T ⊆ A j → T.Nonempty →
    additive_valuation s T ≤ B i →
    ∃ g ∈ T, additive_valuation (v i) (T.erase g) ≤ additive_valuation (v i) (A i)
