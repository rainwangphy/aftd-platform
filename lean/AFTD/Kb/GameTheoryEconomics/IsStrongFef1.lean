import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_strong_fef1

Topic: fair_division   Node: 13648119812a

Provenance: formalization of a published result. Source: arXiv:2611.34488, Definition 2.2

An allocation A satisfies strong FEF1 if for every agent i and every nonempty target D for i, there exists a good g ∈ D such that for every feasible subset T ⊆ D without g with T ∈ F i, agent i values A i at least as much as T.
-/

/-- An allocation satisfies strong FEF1 if for every agent i and nonempty target D, some good g ∈ D eliminates envy towards all feasible subsets of D \ {g}. -/
def is_strong_fef1 {m n : ℕ} (v : Fin n → Fin m → ℝ) (F : Fin n → Set (Finset (Fin m)))
    (A : Fin n → Finset (Fin m)) : Prop := ∀ (i : Fin n) (D : Finset (Fin m)), is_target A i D → D.Nonempty →
    ∃ g ∈ D, ∀ T ⊆ D.erase g, T ∈ F i →
      additive_valuation (v i) T ≤ additive_valuation (v i) (A i)
