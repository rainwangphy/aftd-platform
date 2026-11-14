import AFTD.Prelude

/-!
# finset_mex

Topic: combinatorial_games   Node: 7704758efad9

Provenance: original. Related work: folklore

The minimum excluded natural number (mex) of a finite set of natural numbers s, defined as the smallest natural number not belonging to s.
-/

/-- The minimum excluded natural number (mex) of a finite set of natural numbers. -/
def finset_mex (s : Finset ℕ) : ℕ := ((List.range (s.card + 1)).find? (fun x => ¬(x ∈ s))).getD 0
