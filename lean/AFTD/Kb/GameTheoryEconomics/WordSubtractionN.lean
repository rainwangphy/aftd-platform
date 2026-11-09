import AFTD.Prelude

/-!
# word_subtraction_N

Topic: combinatorial_games   Node: 0b05d6d98763

Provenance: formalization of a published result. Source: arXiv:2611.09157 Section 1.3

For an alphabet α and a finite subtraction set S of lists over α, word_subtraction_N S is the language of winning positions (N-positions) in normal play, where a word w is winning if and only if there exist a word s in S and a prefix u such that w = u ++ s and u is not winning.
-/

/-- The language of winning positions in the normal-play word subtraction game with subtraction set S. -/
def word_subtraction_N {α : Type*} (S : Finset (List α)) : Language α := { w | WellFounded.fix (measure List.length).wf (fun w rec => ∃ s ∈ S, ∃ u : List α, ∃ (h : u.length < w.length), w = u ++ s ∧ ¬ rec u h) w }
