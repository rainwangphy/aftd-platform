import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# ArrowsEmptyPos

Topic: combinatorial_games   Node: 1d88f38967f6

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

The empty starting position in ArrowsPos V whose boolean relation is everywhere false.
-/

/-- The empty starting position with every entry false. -/
def ArrowsEmptyPos (V : Type*) : ArrowsPos V := ⟨fun _ _ => false, fun _ _ h => nomatch h⟩
