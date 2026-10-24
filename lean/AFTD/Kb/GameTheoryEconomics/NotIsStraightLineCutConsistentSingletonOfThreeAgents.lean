import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# not_is_straight_line_cut_consistent_singleton_of_three_agents

Topic: fair_division   Node: 245e3d61aece

Provenance: helper lemma. arXiv:2610.27956, Section 2 (supporting OP-437)

Let P be a finite set of points in ℝ², ℓ a straight line, and α : ℝ² → Fin 3 an allocation function. If every agent in Fin 3 receives at least one point in P (that is, for each i in Fin 3 there exists p in P with α p = i), then α cannot be consistent with the singleton set of lines {ℓ} on P.
-/

/-- A single straight line cannot consistently partition a point set among three non-empty agent shares. -/
theorem not_is_straight_line_cut_consistent_singleton_of_three_agents
    (P : Finset (ℝ × ℝ)) (ℓ : StraightLine) (α : (ℝ × ℝ) → Fin 3)
    (h_surj : ∀ i : Fin 3, ∃ p ∈ P, α p = i) :
    ¬ is_straight_line_cut_consistent P {ℓ} α := by
  intro ⟨s, _, h2⟩
  rcases h_surj 0 with ⟨p0, hp0, hα0⟩
  rcases h_surj 1 with ⟨p1, hp1, hα1⟩
  rcases h_surj 2 with ⟨p2, hp2, hα2⟩
  have h_same : ∀ p q, s ℓ p = s ℓ q → (∀ ℓ' ∈ ({ℓ} : Finset StraightLine), s ℓ' p = s ℓ' q) := by
    intro p q h ℓ' hℓ'
    rw [Finset.mem_singleton.mp hℓ']
    exact h
  have h_cases : s ℓ p0 = s ℓ p1 ∨ s ℓ p0 = s ℓ p2 ∨ s ℓ p1 = s ℓ p2 := by
    cases s ℓ p0 <;> cases s ℓ p1 <;> cases s ℓ p2 <;> decide
  rcases h_cases with h01 | h02 | h12
  · have := h2 p0 hp0 p1 hp1 (h_same p0 p1 h01)
    rw [hα0, hα1] at this
    revert this; decide
  · have := h2 p0 hp0 p2 hp2 (h_same p0 p2 h02)
    rw [hα0, hα2] at this
    revert this; decide
  · have := h2 p1 hp1 p2 hp2 (h_same p1 p2 h12)
    rw [hα1, hα2] at this
    revert this; decide
