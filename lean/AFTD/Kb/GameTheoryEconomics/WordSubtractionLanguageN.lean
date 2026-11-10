import AFTD.Prelude

/-!
# word_subtraction_language_N

Topic: combinatorial_games   Node: b4e0b1ccfb79

Provenance: formalization of a published result. Source: arXiv:2611.09157 Definition 1.5

For an alphabet α and a language S over α, word_subtraction_language_N S is the language of winning positions (N-positions) in the normal-play word subtraction game with subtraction set S, where a word w is an N-position if and only if there exist a word s in S and a prefix u such that w = u ++ s and u is not an N-position.
-/

/-- The language of winning positions (N-positions) in the normal-play word subtraction game with subtraction set S. -/
def word_subtraction_language_N {α : Type*} (S : Language α) : Language α := { w | WellFounded.fix (measure List.length).wf
    (fun (w : List α) (rec : ∀ y, (measure List.length).rel y w → Prop) =>
      ∃ s ∈ S, ∃ u : List α, ∃ (h : u.length < w.length), w = u ++ s ∧ ¬ rec u h) w }
