import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseSubsetAux

/-!
# op75_parse_subset

Topic: np_completeness   Node: eef5230a3f14

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

Decode a canonical subset-sum bit string, rejecting malformed or trailing data.
-/

def op75_parse_subset (w : List Bool) : Option (List ℕ × ℕ) :=
  op75_parse_subset_aux (w.length + 1) w
