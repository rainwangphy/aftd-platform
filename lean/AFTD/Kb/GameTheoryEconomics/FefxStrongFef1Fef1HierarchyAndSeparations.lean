import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsHereditary
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.IsFef1
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1
import AFTD.Kb.GameTheoryEconomics.IsFefx
import AFTD.Kb.GameTheoryEconomics.FefxImpliesStrongFef1
import AFTD.Kb.GameTheoryEconomics.StrongFef1ImpliesFef1
import AFTD.Kb.GameTheoryEconomics.ExistsFef1NotStrongFef1OneAgent
import AFTD.Kb.GameTheoryEconomics.ExistsStrongFef1NotFefxOneAgent

/-!
# fefx_strong_fef1_fef1_hierarchy_and_separations

Topic: fair_division   Node: d1571f8f5b23

Provenance: formalization of a published result. Source: arXiv:2611.34488, Proposition 2.4

Proposition 2.4: Every FEFx allocation satisfies strong FEF1, every allocation satisfying strong FEF1 under nonnegative additive valuations and hereditary feasibility is FEF1, and neither converse holds, even for one agent and goods of unit size under budget constraints.
-/

/-- Hierarchy and separations between FEFx, strong FEF1, and FEF1. -/
theorem fefx_strong_fef1_fef1_hierarchy_and_separations :
    (∀ (m n : ℕ) (v : Fin n → Fin m → ℝ) (F : Fin n → Set (Finset (Fin m)))
      (A : Fin n → Finset (Fin m)),
      is_fefx v F A → is_strong_fef1 v F A) ∧
    (∀ (m n : ℕ) (v : Fin n → Fin m → ℝ) (_hv : ∀ i g, 0 ≤ v i g)
      (F : Fin n → Set (Finset (Fin m))) (_hF : ∀ i, is_hereditary (F i))
      (A : Fin n → Finset (Fin m)),
      is_strong_fef1 v F A → is_fef1 v F A) ∧
    (∃ (m : ℕ) (v : Fin 1 → Fin m → ℝ) (_hv : ∀ i g, 0 ≤ v i g)
      (B : ℝ) (A : Fin 1 → Finset (Fin m)),
      let F : Fin 1 → Set (Finset (Fin m)) := fun _ => {S | (S.card : ℝ) ≤ B}
      (∀ i, is_hereditary (F i)) ∧
      is_fef1 v F A ∧ ¬ is_strong_fef1 v F A) ∧
    (∃ (m : ℕ) (v : Fin 1 → Fin m → ℝ) (_hv : ∀ i g, 0 ≤ v i g)
      (B : ℝ) (A : Fin 1 → Finset (Fin m)),
      let F : Fin 1 → Set (Finset (Fin m)) := fun _ => {S | (S.card : ℝ) ≤ B}
      (∀ i, is_hereditary (F i)) ∧
      is_strong_fef1 v F A ∧ ¬ is_fefx v F A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    exact fefx_implies_strong_fef1
  · intro m n
    exact strong_fef1_implies_fef1
  · exact exists_fef1_not_strong_fef1_one_agent
  · exact exists_strong_fef1_not_fefx_one_agent
