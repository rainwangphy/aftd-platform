import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RegularWordSubtractionGameStep

/-!
# regular_word_subtraction_game_subset_step

Topic: combinatorial_games   Node: 7fbc2651c7cb

Provenance: helper lemma. step towards op_1677_regular_word_subtraction_state_complexity_ge

The subset-construction transition: from a set S of DFA states and a letter c, take the image of S under the subtraction DFA step, and add the image of the start state 0 only if 2 ∉ S.
-/

/-- Subset-construction step: image the current set under the DFA step, and add the fresh start-state image unless the state 2 is already present (a P-position prefix kills the move). -/
noncomputable def regular_word_subtraction_game_subset_step (N : ℕ) (hN : 3 ≤ N) (S : Finset (Fin (N + 1))) (c : Bool) : Finset (Fin (N + 1)) := (if (⟨2, by omega⟩ : Fin (N + 1)) ∈ S then ∅
      else {(regular_word_subtraction_game_step N hN ⟨0, by omega⟩ c)})
     ∪ S.image (fun q => regular_word_subtraction_game_step N hN q c)
