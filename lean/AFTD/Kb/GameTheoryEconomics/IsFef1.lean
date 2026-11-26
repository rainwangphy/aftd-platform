import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fef1

Topic: fair_division   Node: 8eae5d4681f8

Provenance: formalization of a published result. Source: arXiv:2611.34488, Definition 2.1

An allocation A is feasibly envy-free up to one good (FEF1) if for every agent i, every target D for i, and every nonempty feasible subset T ⊆ D with T ∈ F i, there exists a good g ∈ T such that agent i values A i at least as much as T without g.
-/

/-- An allocation is FEF1 if for every agent i, target D, and nonempty feasible T ⊆ D, removing some good from T eliminates envy. -/
def is_fef1 {m n : ℕ} (v : Fin n → Fin m → ℝ) (F : Fin n → Set (Finset (Fin m)))
    (A : Fin n → Finset (Fin m)) : Prop := ∀ (i : Fin n) (D : Finset (Fin m)), is_target A i D →
    ∀ T ⊆ D, T.Nonempty → T ∈ F i →
      ∃ g ∈ T, additive_valuation (v i) (T.erase g) ≤ additive_valuation (v i) (A i)
