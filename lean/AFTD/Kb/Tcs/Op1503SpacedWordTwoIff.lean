import AFTD.Prelude
import AFTD.Kb.Tcs.IsTSpacedWord
import AFTD.Kb.Tcs.IsSquarePathColoring

/-!
# op_1503_spaced_word_two_iff

Topic: information   Node: 72065599b8ad

Provenance: helper lemma. knowledgebase, OP-1503

For any word y : Fin n → Fin q, y is 2-spaced if and only if y is a proper coloring of the square of the path (is_square_path_coloring y).
-/

/-- Equivalence of 2-spacing and square-path proper coloring. -/
theorem op_1503_spaced_word_two_iff {n q : ℕ} (y : Fin n → Fin q) :
    is_t_spaced_word 2 y ↔ is_square_path_coloring y := by
  constructor
  · intro h i j hij
    exact h i j (by omega) (by omega)
  · intro h i j hlt hle
    exact h i j (by omega)
