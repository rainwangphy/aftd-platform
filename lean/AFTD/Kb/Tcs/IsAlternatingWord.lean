import AFTD.Prelude
import AFTD.Kb.Tcs.AlternatingWord

/-!
# is_alternating_word

Topic: information   Node: 1c5bd5ed1c2b

Provenance: formalization of a published result. Source: arXiv:2611.01064, Section 2

For a function w : Fin n → Bool, is_alternating_word w asserts that w equals alternating_word n false or w equals alternating_word n true.
-/

/-- Predicate asserting that a binary word of length n is one of the two alternating words. -/
def is_alternating_word {n : ℕ} (w : Fin n → Bool) : Prop := w = alternating_word n false ∨ w = alternating_word n true
