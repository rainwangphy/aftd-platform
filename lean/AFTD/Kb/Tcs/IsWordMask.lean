import AFTD.Prelude
import AFTD.Kb.Tcs.WordProj

/-!
# is_word_mask

Topic: automata   Node: 4bae70b425f0

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3

A binary mask of a word with respect to sources u and v has the same length as the word and projects to u on true and to v on false.
-/

/-- A binary mask M of word w with respect to source words u and v. -/
def is_word_mask {α : Type*} (u v w : List α) (M : List Bool) : Prop :=
  M.length = w.length ∧ word_proj true w M = u ∧ word_proj false w M = v
