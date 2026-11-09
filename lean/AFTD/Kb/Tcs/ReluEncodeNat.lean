import AFTD.Prelude

/-!
# relu_encode_nat

Topic: np_completeness   Node: 526c53a9bda7

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Binary encoding of a natural number as a self-delimiting Bool word: each base-2 digit, least significant first, is preceded by a true marker, and the word ends with false.
-/

def relu_encode_nat (n : ℕ) : List Bool :=
  (Nat.digits 2 n).flatMap (fun d => [true, decide (d = 1)]) ++ [false]
