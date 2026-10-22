import AFTD.Prelude

/-!
# scoring_last

Topic: social_choice   Node: afc1b197c8be

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 1

Given a natural number m with 2 ≤ m and a scoring vector s : Fin m → ℚ, scoring_last m hm s is the value of s at the last index m - 1.
-/

/-- The score awarded to the last index m - 1 by scoring vector s. -/
def scoring_last (m : ℕ) (hm : 2 ≤ m) (s : Fin m → ℚ) : ℚ :=
  s ⟨m - 1, by omega⟩
