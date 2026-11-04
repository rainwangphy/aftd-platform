import AFTD.Prelude
import AFTD.Kb.Tcs.TwoInsertionCollision

/-!
# min_two_insertion_collision

Topic: information   Node: 90604bccae10

Provenance: original. Related work: arXiv:2611.01064, Section 2

For a natural number n, min_two_insertion_collision n is the minimum over all binary words w of length n of two_insertion_collision (n - 2) w if 2 ≤ n, and 0 otherwise.
-/

/-- The minimum two-insertion collision sum C_n over all binary words of length n. -/
def min_two_insertion_collision (n : ℕ) : ℕ := if 2 ≤ n then
    (Finset.univ.image (fun w : Fin (n - 2 + 2) → Bool => two_insertion_collision (n - 2) w)).min'
      (Finset.Nonempty.image Finset.univ_nonempty _)
  else 0
