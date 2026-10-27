import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowView
import AFTD.Kb.GameTheoryEconomics.RowViewOfSage
import AFTD.Kb.GameTheoryEconomics.RowMultiset

/-!
# RowProtocolSolves

Topic: combinatorial_games   Node: c88fe4b43161

Provenance: formalization of a published result. Source: arXiv:2610.33032:180

A protocol p : RowLocalView (Fin S) → α solves the anonymous-slip puzzle for S sages in a row with 2 ≤ S without seat labels if for every sage x : Fin S and all seatings π₁ π₂ : Equiv.Perm (Fin S) such that rowViewOfSage hS π₁ x = rowViewOfSage hS π₂ x, if rowMultiset hS p π₁ = rowMultiset hS p π₂ then π₁ = π₂.
-/

/-- A protocol solves the unlabeled row anonymous-slip puzzle if every sage can uniquely recover the true seating. -/
def RowProtocolSolves (S : ℕ) {α : Type*} (hS : 2 ≤ S) (p : RowLocalView (Fin S) → α) : Prop := ∀ (x : Fin S) (π₁ π₂ : Equiv.Perm (Fin S)),
    rowViewOfSage hS π₁ x = rowViewOfSage hS π₂ x →
    rowMultiset hS p π₁ = rowMultiset hS p π₂ →
    π₁ = π₂
