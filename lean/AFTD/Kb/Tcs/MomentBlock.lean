import AFTD.Prelude
import AFTD.Kb.Tcs.MomentElem

/-!
# moment_block

Topic: combinatorics   Node: 70f10c739835

Provenance: helper lemma. step towards infinite_bh_set_upper_density_eq_one_div_h

The finite moment-curve block `B_q = {moment_elem h q h a | 0 ≤ a < q}`: the `q` residues encoded in `h` base-`h*q` digits.
-/

/-- The set of `h`-digit moment-curve encodings of the `q` residues. -/
def moment_block (h q : ℕ) : Finset ℕ := (Finset.range q).image (moment_elem h q h)
