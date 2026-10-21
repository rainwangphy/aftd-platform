import AFTD.Prelude

/-!
# parityCharacter

Topic: circuits   Node: c09df49e7c7a

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2.3 and Listing A.13

For an implicit natural number n and a Boolean assignment x : Fin n → Bool, parityCharacter x is the real number defined by the product over all i : Fin n of (if x i then (1 : ℝ) else -1).
-/

/-- The alternating-sign parity character χ(x) = ∏_{i=1}^n (2x_i - 1). -/
def parityCharacter {n : ℕ} (x : Fin n → Bool) : ℝ := ∏ i : Fin n, (if x i then (1 : ℝ) else -1)
