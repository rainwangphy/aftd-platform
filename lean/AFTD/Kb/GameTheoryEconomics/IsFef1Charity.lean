import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Charity
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fef1_charity

Topic: fair_division   Node: 0220bca74113

Provenance: formalization of a published result. Source: arXiv:2611.34488 Def. 2.1

Given common item sizes s : Fin m → ℝ, individual agent budgets B : Fin n → ℝ, and additive valuations given by item values v : Fin n → Fin m → ℝ, an allocation A : Fin n → Finset (Fin m) satisfies FEF1 towards the charity if for every agent i in Fin n and every nonempty subset T ⊆ charity A with total size additive_valuation s T ≤ B i, there exists a good g ∈ T such that additive_valuation (v i) (T.erase g) ≤ additive_valuation (v i) (A i).
-/

/-- FEF1 towards the charity bundle under common item sizes and individual budgets. -/
def is_fef1_charity {m n : ℕ} (s : Fin m → ℝ) (B : Fin n → ℝ)
    (v : Fin n → Fin m → ℝ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i : Fin n, ∀ T : Finset (Fin m), T ⊆ charity A → T.Nonempty →
    additive_valuation s T ≤ B i →
    ∃ g ∈ T, additive_valuation (v i) (T.erase g) ≤ additive_valuation (v i) (A i)
