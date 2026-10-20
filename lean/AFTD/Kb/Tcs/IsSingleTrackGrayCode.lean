import AFTD.Prelude

/-!
# is_single_track_gray_code

Topic: combinatorics   Node: b5586666b4b8

Provenance: original. Related work: arXiv:2610.24758: Optimal single-track Gray codes from Gray-ordered necklaces

A sequence w of n-bit words is a single-track Gray code of length n and period P if it is periodic with period P, all words within a period are distinct, consecutive words differ in exactly one bit, and every column is a cyclic shift of the first column.
-/

/-- Predicate asserting that w is a single-track Gray code of length n and period P. -/
def is_single_track_gray_code (n P : ℕ) (w : ℕ → ℕ) : Prop :=
  (∀ t, w (t + P) = w t) ∧
  (∀ t, w t < 2 ^ n) ∧
  (∀ t₁ t₂, t₁ < P → t₂ < P → w t₁ = w t₂ → t₁ = t₂) ∧
  (∀ t, ∃ i < n, w (t + 1) ^^^ w t = 2 ^ i) ∧
  ∃ h : ℕ → ℕ, h 0 = 0 ∧
    ∀ t, ∀ j < n, Nat.testBit (w t) j = Nat.testBit (w (t + h j)) 0
