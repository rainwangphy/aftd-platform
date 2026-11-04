import AFTD.Prelude

/-!
# zmod_clockwise_dist

Topic: combinatorics   Node: ab4d2e0f3c7a

Provenance: formalization of a published result. Source: arXiv:2611.02684, Section B.1, p. 34

For any natural number n and any elements s, r in ZMod n, the clockwise distance from s to r is the integer (r - s) mod n, viewed as a real number.
-/

/-- The clockwise distance c(s, r) = (r - s) mod n from s to r on ZMod n. -/
def zmod_clockwise_dist {n : ℕ} (s r : ZMod n) : ℝ := ((r - s).val : ℝ)
