import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_subset_encoding

Topic: np_completeness   Node: 11b6c98390af

Provenance: helper lemma. OP-75 one-pass subset-sum construction, arXiv:2610.06092; binary source encoding for a machine-level reduction.

The source word encodes each nonnegative integer weight as a true marker followed by its self-delimiting natural encoding, then a false marker and the target natural encoding.
-/

def op75_subset_encoding (as : List ℕ) (t : ℕ) : List Bool := (as.flatMap fun a => true :: relu_encode_nat a) ++ [false] ++ relu_encode_nat t
