import AFTD.Prelude

/-!
# word_proj

Topic: automata   Node: d9354e935b68

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3

The projection of a word under a binary mask keeps only the letters at positions where the mask equals a given target boolean.
-/

/-- Projection of a word onto the positions where the binary mask equals target. -/
def word_proj {α : Type*} (target : Bool) : List α → List Bool → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, b :: bs => if b == target then x :: word_proj target xs bs else word_proj target xs bs
