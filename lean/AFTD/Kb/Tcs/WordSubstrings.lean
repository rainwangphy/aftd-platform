import AFTD.Prelude

/-!
# word_substrings

Topic: approximation   Node: c42589eb8da6

Provenance: formalization of a published result. Source: arXiv:2611.15074, Section 3.2, lines 808-812

The set Sub(w) of substrings of a word w of length at least 2.
-/

/-- Substrings of a list of length at least 2. -/
def word_substrings {α : Type*} (w : List α) : Set (List α) := {u | u <:+: w ∧ 2 ≤ u.length}
