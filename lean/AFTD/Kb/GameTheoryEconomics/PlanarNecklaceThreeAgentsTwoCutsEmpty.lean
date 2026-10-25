import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# planar_necklace_three_agents_two_cuts_empty

Topic: fair_division   Node: 641bd16e8b0d

Provenance: helper lemma. step towards planar_necklace_three_agents_two_cuts

The empty point set in the plane can be trivially fairly divided among 3 agents with at most 2 straight-line cuts (0 cuts suffice).
-/

/-- The empty point set in the plane can be trivially fairly divided among 3 agents with at most 2 straight lines. -/
theorem planar_necklace_three_agents_two_cuts_empty
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2)
    (hP : P = ∅) :
    ∃ (L : Finset StraightLine) (α : (ℝ × ℝ) → Fin 3),
      L.card ≤ 2 ∧
      is_straight_line_cut_consistent P L α ∧
      ∀ i : Fin 3,
        (P.filter (fun p => α p = i ∧ c p = 0)).card = (P.filter (fun p => c p = 0)).card / 3 ∧
        (P.filter (fun p => α p = i ∧ c p = 1)).card = (P.filter (fun p => c p = 1)).card / 3 := by
  subst hP
  refine ⟨∅, fun _ => 0, by simp, ?_, by simp⟩
  unfold is_straight_line_cut_consistent
  refine ⟨fun _ _ => false, by simp, by simp⟩
