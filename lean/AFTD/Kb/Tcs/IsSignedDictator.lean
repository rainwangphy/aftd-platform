import AFTD.Prelude

/-!
# is_signed_dictator

Topic: information   Node: 0a84386a2931

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:150

For a natural number n, a real-valued function g : (Fin n → Bool) → ℝ is a signed dictator if there exist an index i : Fin n and a real number s : ℝ with s = 1 ∨ s = -1 such that for all x : Fin n → Bool, g x = s * (if x i then -1 else 1).
-/

/-- Predicate that a function g : (Fin n → Bool) → ℝ is a signed dictator. -/
def is_signed_dictator (n : ℕ) (g : (Fin n → Bool) → ℝ) : Prop := ∃ (i : Fin n) (s : ℝ), (s = 1 ∨ s = -1) ∧ ∀ x, g x = s * (if x i then -1 else 1)
