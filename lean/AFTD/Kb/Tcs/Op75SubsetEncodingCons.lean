import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_subset_encoding_cons

Topic: np_completeness   Node: 56da7c811a2d

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

Encoding a nonempty weight list emits its marker, the head natural, then the remaining instance.
-/

theorem op75_subset_encoding_cons (a : ℕ) (as : List ℕ) (t : ℕ) :
    op75_subset_encoding (a :: as) t = true :: (relu_encode_nat a ++ op75_subset_encoding as t) := by
  simp [op75_subset_encoding, List.append_assoc]
