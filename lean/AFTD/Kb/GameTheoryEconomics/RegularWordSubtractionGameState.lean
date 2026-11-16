import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RegularWordSubtractionGameSubsetStep

/-!
# regular_word_subtraction_game_state

Topic: combinatorial_games   Node: bac83531db82

Provenance: helper lemma. step towards op_1677_regular_word_subtraction_state_complexity_ge

G(w), the subset-construction state of the word w: fold the subset step from the empty set along w. Its members are the DFA states reached by suffixes s of w whose complementary prefix is a P-position, and 2 ∈ G(w) iff w is an N-position.
-/

/-- G(w): the subset-construction state reached from ∅ by folding the subset step along w. -/
noncomputable def regular_word_subtraction_game_state (N : ℕ) (hN : 3 ≤ N) (w : List Bool) : Finset (Fin (N + 1)) := w.foldl (fun S c => regular_word_subtraction_game_subset_step N hN S c) ∅
