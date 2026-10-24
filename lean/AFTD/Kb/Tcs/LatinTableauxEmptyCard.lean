import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTableaux

/-!
# latin_tableaux_empty_card

Topic: combinatorics   Node: 380c5403c3a7

Provenance: helper lemma. arXiv:2610.29291

The number of Latin tableaux on the empty Young diagram is 1.
-/

/-- The empty Young diagram has exactly one Latin tableau. -/
theorem latin_tableaux_empty_card : (latin_tableaux (⊥ : YoungDiagram)).card = 1 := by
  simp [latin_tableaux]
