import AFTD.Prelude

/-!
# word_suffixes

Topic: approximation   Node: d242e2024eaf

Provenance: formalization of a published result. Source: arXiv:2611.15074, Section 3.2, lines 808-812

The set Suf(w) of nonempty suffixes of a word w.
-/

/-- Nonempty suffixes of a list. -/
def word_suffixes {α : Type*} (w : List α) : Set (List α) := {u | u <:+ w ∧ u ≠ []}
