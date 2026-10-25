import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistentOfParallelCuts

/-!
# planar_necklace_three_agents_two_cuts_of_fair_parallel_cuts

Topic: fair_division   Node: 688175ad0bea

Provenance: helper lemma. step towards planar_necklace_three_agents_two_cuts

If a finite point set P admits a fair 3-way partition by two parallel cuts with non-zero linear functional φ and thresholds t₁ < t₂, then there exists a set of at most 2 straight lines and an allocation consistent with those lines achieving the same fair shares.
-/

/-- If a point set admits a fair 3-way partition by two parallel cuts with thresholds t₁ < t₂, then there exists a set of at most 2 straight lines and an allocation consistent with those lines achieving the same fair shares. -/
theorem planar_necklace_three_agents_two_cuts_of_fair_parallel_cuts
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2)
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (t₁ t₂ : ℝ) (ht : t₁ < t₂)
    (α : (ℝ × ℝ) → Fin 3)
    (hα : ∀ p ∈ P, (α p = 0 → φ p ≤ t₁) ∧ (α p = 1 → t₁ ≤ φ p ∧ φ p ≤ t₂) ∧ (α p = 2 → t₂ ≤ φ p))
    (h_fair : ∀ i : Fin 3,
      (P.filter (fun p => α p = i ∧ c p = 0)).card = (P.filter (fun p => c p = 0)).card / 3 ∧
      (P.filter (fun p => α p = i ∧ c p = 1)).card = (P.filter (fun p => c p = 1)).card / 3) :
    ∃ (L : Finset StraightLine) (α' : (ℝ × ℝ) → Fin 3),
      L.card ≤ 2 ∧
      is_straight_line_cut_consistent P L α' ∧
      ∀ i : Fin 3,
        (P.filter (fun p => α' p = i ∧ c p = 0)).card = (P.filter (fun p => c p = 0)).card / 3 ∧
        (P.filter (fun p => α' p = i ∧ c p = 1)).card = (P.filter (fun p => c p = 1)).card / 3 := by
  obtain ⟨L, hL, hcons⟩ := is_straight_line_cut_consistent_of_parallel_cuts P φ hφ t₁ t₂ α ht hα
  exact ⟨L, α, hL, hcons, h_fair⟩
