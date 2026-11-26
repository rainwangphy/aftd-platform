import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fefx

Topic: fair_division   Node: 3c213b5b9f58

Provenance: formalization of a published result. Source: arXiv:2611.34488, Definition 2.3

An allocation A is FEFx (1-FEFx) if for every agent i, every target D for i, and every feasible proper subset T ⊂ D with T ∈ F i, agent i values A i at least as much as T.
-/

/-- An allocation is FEFx if every agent values their bundle at least as much as any feasible proper subset of any target. -/
def is_fefx {m n : ℕ} (v : Fin n → Fin m → ℝ) (F : Fin n → Set (Finset (Fin m)))
    (A : Fin n → Finset (Fin m)) : Prop := ∀ (i : Fin n) (D : Finset (Fin m)), is_target A i D →
    ∀ T : Finset (Fin m), T ⊂ D → T ∈ F i →
      additive_valuation (v i) T ≤ additive_valuation (v i) (A i)
