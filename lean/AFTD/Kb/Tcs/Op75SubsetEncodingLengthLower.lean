import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_subset_encoding_length_lower

Topic: np_completeness   Node: 43451f49e722

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

The number of weights is at most the bit length of the encoded instance.
-/

lemma op75_subset_encoding_length_lower (as : List ℕ) (t : ℕ) :
    as.length ≤ (op75_subset_encoding as t).length := by
  have h : as.length ≤ (as.flatMap (fun a => true :: relu_encode_nat a)).length := by
    induction as with
    | nil => simp
    | cons a as ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append] at *
        omega
  simp only [op75_subset_encoding, List.length_append, List.length_cons, List.length_nil]
  omega
