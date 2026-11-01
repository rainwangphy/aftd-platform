import AFTD.Prelude

/-!
# ternary_axis_line

Topic: combinatorics   Node: 19525fe5a9b5

Provenance: helper lemma. step towards ternary_minimal_line_cover_first_gap_empty

The axis-parallel ternary line of direction i through c: the three points of (Fin n → ZMod 3) obtained from c by overwriting coordinate i with each t ∈ ZMod 3.
-/

/-- The three-point axis-parallel line of direction `i` through `c`. -/
def ternary_axis_line (n : ℕ) (i : Fin n) (c : Fin n → ZMod 3) : Finset (Fin n → ZMod 3) := Finset.univ.image (fun t : ZMod 3 => Function.update c i t)
