import AFTD.Prelude

/-!
# is_token_segmentation

Topic: approximation   Node: 9fb9280f6ab6

Provenance: formalization of a published result. Source: arXiv:2611.15074, Section 2.1, lines 213-216

A list of tokens forms a valid segmentation of a word y over vocabulary V and single-character alphabet if their concatenation is y and each token belongs to V or has length 1.
-/

/-- Predicate that a list of tokens is a valid segmentation over vocabulary V and singletons. -/
def is_token_segmentation {α : Type*} (V : Set (List α)) (y : List α) (tokens : List (List α)) : Prop := tokens.flatten = y ∧ ∀ t ∈ tokens, t ∈ V ∨ t.length = 1
