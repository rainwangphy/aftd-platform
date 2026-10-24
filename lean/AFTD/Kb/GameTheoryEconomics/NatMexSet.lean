import AFTD.Prelude

/-!
# nat_mex_set

Topic: combinatorial_games   Node: 5648263f50aa

Provenance: original. Related work: folklore

The minimum excluded natural number of a set s of natural numbers is the infimum of the set of natural numbers not in s.
-/

/-- The minimum excluded natural number (mex) of a set of natural numbers. -/
noncomputable def nat_mex_set (s : Set ℕ) : ℕ := sInf {n : ℕ | n ∉ s}
