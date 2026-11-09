import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WordSubtractionBuffer
import AFTD.Kb.GameTheoryEconomics.WordSubtractionN

/-!
# word_subtraction_inv

Topic: combinatorial_games   Node: e8c7d3e2ebac

Provenance: helper lemma. step towards word_subtraction_is_regular

The state invariant: the buffer is the reverse window of w, and for each j ≤ n the status bit j is true exactly when j exceeds the length of w or the prefix of w of length w.length - j is a winning position.
-/

/-- Correctness invariant of the state relative to the word read so far. -/
def word_subtraction_inv {α : Type*} (S : Finset (List α)) (n : ℕ) (w : List α)
    (st : (Fin n → Option α) × (Fin (n + 1) → Bool)) : Prop := st.1 = word_subtraction_buffer n w ∧
    ∀ j : Fin (n + 1),
      (st.2 j = true ↔ ((j : ℕ) > w.length ∨ w.take (w.length - (j : ℕ)) ∈ word_subtraction_N S))
