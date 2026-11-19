import AFTD.Prelude

/-!
# odd_succ_of_even

Topic: graphs   Node: 7eab3b550ec9

Provenance: helper lemma. folklore

If k is an even natural number, then k + 1 is an odd natural number.
-/

/-- The successor of an even natural number is odd. -/
theorem odd_succ_of_even {k : ℕ} (h : Even k) : Odd (k + 1) := Even.add_one h
