import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseSubset
import AFTD.Kb.Tcs.Op75ParseSubsetAuxSound
import AFTD.Kb.Tcs.Op75ParseSubsetAuxComplete
import AFTD.Kb.Tcs.Op75SubsetEncodingLengthLower
import AFTD.Kb.Tcs.Op75SubsetEncoding

/-!
# op75_parse_subset_spec

Topic: np_completeness   Node: 380897d1a1c4

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

The total decoder returns a weight list and target exactly when their canonical encoding equals its input.
-/

theorem op75_parse_subset_spec (w : List Bool) (as : List ℕ) (t : ℕ) :
    op75_parse_subset w = some (as, t) ↔ op75_subset_encoding as t = w := by
  constructor
  · intro h
    exact op75_parse_subset_aux_sound (w.length+1) w as t h
  · intro h
    subst w
    unfold op75_parse_subset
    apply op75_parse_subset_aux_complete
    have hs := op75_subset_encoding_length_lower as t
    omega
