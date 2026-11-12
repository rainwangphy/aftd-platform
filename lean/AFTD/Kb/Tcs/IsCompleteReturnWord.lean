import AFTD.Prelude

/-!
# is_complete_return_word

Topic: combinatorics   Node: 40c4ed7a2067

Provenance: formalization of a published result. Source: arXiv:2611.13676 Section 2

A word c is a complete return word to a factor q if q is both a prefix and a suffix of c, strictly shorter than c, and q does not occur at any intermediate position in c.
-/

/-- A word c is a complete return word to factor q if q is a prefix and suffix of c, |c| > |q|, and q has no internal occurrences in c. -/
def is_complete_return_word {α : Type*} (c q : List α) : Prop := q <+: c ∧ q <:+ c ∧ q.length < c.length ∧
  ∀ i : ℕ, 0 < i → i < c.length - q.length → ¬ (q <+: c.drop i)
