import AFTD.Prelude

/-!
# nat_self_delimiting_code

Topic: computability   Node: 4305f3dbb29b

Provenance: helper lemma. Input/output encoding for the polynomial-time statement of OP-851 (arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 8, open question (1)); a standard prefix-free binary code of naturals.

The self-delimiting binary code of a natural number m: each bit b of the binary expansion of m (least significant bit first, as in Nat.bits, so 0 has no bits) is written as the two bits true, b, and the code ends with a single false.
-/

def nat_self_delimiting_code (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]
