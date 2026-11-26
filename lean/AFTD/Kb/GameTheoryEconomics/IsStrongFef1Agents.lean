import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_strong_fef1_agents

Topic: fair_division   Node: ac9090ce1d4a

Provenance: formalization of a published result. Source: arXiv:2611.34488 Def. 2.2

Given common item sizes s : Fin m → ℝ, individual agent budgets B : Fin n → ℝ, and additive valuations given by item values v : Fin n → Fin m → ℝ, an allocation A : Fin n → Finset (Fin m) satisfies strong FEF1 between agents if for every pair of distinct agents i ≠ j in Fin n such that A j is nonempty, there exists a good g ∈ A j such that for every subset T ⊆ (A j).erase g with total size additive_valuation s T ≤ B i, additive_valuation (v i) T ≤ additive_valuation (v i) (A i).
-/

/-- Strong FEF1 between agents under common item sizes and individual budgets. -/
def is_strong_fef1_agents {m n : ℕ} (s : Fin m → ℝ) (B : Fin n → ℝ)
    (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j : Fin n, i ≠ j → (A j).Nonempty →
    ∃ g ∈ A j, ∀ T : Finset (Fin m), T ⊆ (A j).erase g →
      additive_valuation s T ≤ B i →
      additive_valuation (v i) T ≤ additive_valuation (v i) (A i)
