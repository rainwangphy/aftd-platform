import AFTD.Prelude

/-!
# harborth_half

Topic: combinatorics   Node: 124cd98b61ee

Provenance: helper lemma. step towards harborth_bound_rank_three_mul_two

Candidate halving map on ZMod (2k), defined as (w.val / 2) cast into ZMod k.
-/

def harborth_half (k : ℕ) (w : ZMod (2 * k)) : ZMod k := ((w.val / 2 : ℕ) : ZMod k)
