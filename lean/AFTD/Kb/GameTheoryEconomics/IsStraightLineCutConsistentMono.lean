import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# is_straight_line_cut_consistent_mono

Topic: fair_division   Node: 6a2441790d12

Provenance: helper lemma. folklore, supporting monotonicity of straight line cut consistency

Let P be a finite set of points in ℝ², L and L' finite sets of straight lines with L ⊆ L', k a natural number, and α : ℝ² → Fin k an allocation function. If α is consistent with L on P, then α is also consistent with L' on P.
-/

/-- Consistency of an allocation with a set of straight lines is monotone under taking supersets of lines. -/
theorem is_straight_line_cut_consistent_mono
    (P : Finset (ℝ × ℝ)) {L L' : Finset StraightLine} {k : ℕ} (α : (ℝ × ℝ) → Fin k)
    (hLL' : L ⊆ L')
    (hcons : is_straight_line_cut_consistent P L α) :
    is_straight_line_cut_consistent P L' α := by
  classical
  rcases hcons with ⟨s, hs_cut, hs_α⟩
  let s' : StraightLine → (ℝ × ℝ) → Bool := fun ℓ p =>
    if ℓ ∈ L then s ℓ p else decide (0 ≤ ℓ.cut p)
  use s'
  constructor
  · intro ℓ hℓ p hp
    by_cases h : ℓ ∈ L
    · simp only [s', if_pos h]
      exact hs_cut ℓ h p hp
    · simp only [s', if_neg h]
      constructor
      · intro hpos
        simp [le_of_lt hpos]
      · intro hneg
        simp [not_le_of_gt hneg]
  · intro p hp q hq hsep
    apply hs_α p hp q hq
    intro ℓ hℓ
    have hℓ' : ℓ ∈ L' := hLL' hℓ
    have := hsep ℓ hℓ'
    simp only [s', if_pos hℓ] at this
    exact this
