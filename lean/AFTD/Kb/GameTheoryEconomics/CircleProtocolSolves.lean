import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CircleLocalView
import AFTD.Kb.GameTheoryEconomics.CircleView
import AFTD.Kb.GameTheoryEconomics.CircleViewOfSage
import AFTD.Kb.GameTheoryEconomics.CircleMultiset

/-!
# CircleProtocolSolves

Topic: combinatorial_games   Node: f817ef207e75

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

Given a natural number S, an implicit type α, a hypothesis hS : 3 ≤ S, and a protocol p : CircleLocalView (Fin S) → α, CircleProtocolSolves S hS p asserts that for all sages x : Fin S and all seatings π₁ π₂ : Equiv.Perm (Fin S), if circleViewOfSage hS π₁ x = circleViewOfSage hS π₂ x and circleMultiset hS p π₁ = circleMultiset hS p π₂, then there exists k : Fin S such that for all i : Fin S, π₁ (i + k) = π₂ i.
-/

/-- Predicate that a protocol solves the circle anonymous-slip puzzle without seat labels. -/
def CircleProtocolSolves (S : ℕ) {α : Type*} (hS : 3 ≤ S) (p : CircleLocalView (Fin S) → α) : Prop :=
  have : NeZero S := ⟨by omega⟩
  ∀ (x : Fin S) (π₁ π₂ : Equiv.Perm (Fin S)),
    circleViewOfSage hS π₁ x = circleViewOfSage hS π₂ x →
    circleMultiset hS p π₁ = circleMultiset hS p π₂ →
    ∃ k : Fin S, ∀ i : Fin S, π₁ (i + k) = π₂ i
