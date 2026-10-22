import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsParallelTwoCutConsistent

/-!
# is_parallel_two_cut_consistent_empty

Topic: fair_division   Node: 78652192d12f

Provenance: helper lemma. folklore

For any linear map φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, thresholds t₁, t₂ ∈ ℝ satisfying t₁ ≤ t₂, and assignment α : (ℝ × ℝ) → Fin 3, the empty set of points in ℝ × ℝ satisfies is_parallel_two_cut_consistent ∅ φ t₁ t₂ α.
-/

/-- The empty set of points is consistent with any two parallel cuts with thresholds t₁ ≤ t₂. -/
theorem is_parallel_two_cut_consistent_empty (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (α : (ℝ × ℝ) → Fin 3) :
    is_parallel_two_cut_consistent ∅ φ t₁ t₂ α := by
  refine ⟨ht, fun p hp => by simp at hp⟩
