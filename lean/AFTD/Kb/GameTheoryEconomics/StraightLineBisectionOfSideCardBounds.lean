import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteColorCutSigning
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# straight_line_bisection_of_side_card_bounds

Topic: fair_division   Node: 5bf4d27dc2a6

Provenance: helper lemma. Boundary-assignment helper for planar_necklace_three_agents_three_cuts; arXiv:2610.27956 Proposition 9 and its bisection step. The definition permits arbitrary signs on zero cuts.

A straight line whose strictly positive and strictly negative sides each contain at most half of each color admits a consistent two-agent allocation giving each agent exactly half of each color. Points on the line fill the separate color quotas.
-/

open Finset

theorem straight_line_bisection_of_side_card_bounds
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2) (ℓ : StraightLine)
    (heven : ∀ j, 2 ∣ (P.filter fun p => c p = j).card)
    (hpos : ∀ j, ((P.filter fun p => c p = j).filter fun p => 0 < ℓ.cut p).card ≤
      (P.filter fun p => c p = j).card / 2)
    (hneg : ∀ j, ((P.filter fun p => c p = j).filter fun p => ℓ.cut p < 0).card ≤
      (P.filter fun p => c p = j).card / 2) :
    ∃ α : (ℝ × ℝ) → Fin 2,
      is_straight_line_cut_consistent P {ℓ} α ∧
      ∀ i j : Fin 2,
        (P.filter fun p => α p = i ∧ c p = j).card =
          (P.filter fun p => c p = j).card / 2 := by
  classical
  obtain ⟨s, hs, hcard⟩ := finite_color_cut_signing P c (fun p => ℓ.cut p)
    heven hpos hneg
  let α := fun p => if s p then (0 : Fin 2) else 1
  refine ⟨α, ⟨fun _ p => s p, ?_, ?_⟩, ?_⟩
  · intro l hl p hp
    have : l = ℓ := mem_singleton.mp hl
    subst l
    exact hs p hp
  · intro p hp q hq heq
    have h := heq ℓ (mem_singleton_self _)
    simp only [α, h]
  · intro i j
    fin_cases i
    · change (P.filter fun p => α p = 0 ∧ c p = j).card = _
      have hfilter : (P.filter fun p => α p = 0 ∧ c p = j) =
          (P.filter fun p => c p = j).filter (fun p => s p = true) := by
        ext p
        cases h : s p <;> simp [α, h, and_left_comm, and_assoc, and_comm]
      rw [hfilter]
      exact (hcard j).1
    · change (P.filter fun p => α p = 1 ∧ c p = j).card = _
      have hfilter : (P.filter fun p => α p = 1 ∧ c p = j) =
          (P.filter fun p => c p = j).filter (fun p => s p = false) := by
        ext p
        cases h : s p <;> simp [α, h, and_left_comm, and_assoc, and_comm]
      rw [hfilter]
      exact (hcard j).2
