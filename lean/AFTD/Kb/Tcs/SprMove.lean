import AFTD.Prelude

/-!
# spr_move

Topic: learning   Node: 0c6e067488b3

Provenance: formalization of a published result. Source: arXiv:2610.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2, steps 2-3 of a round

The board after the labeler empties the cells of a set R and places the sign s in the selected cell j.
-/

/-- The board after the labeler empties the cells of `R` and places sign `s` in cell `j`. -/
def spr_move {n : ℕ} (b : Fin n → Option Bool) (j : Fin n) (R : Finset (Fin n)) (s : Bool) :
    Fin n → Option Bool :=
  fun i => if i = j then some s else if i ∈ R then none else b i
