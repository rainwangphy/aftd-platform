import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# rat_self_delimiting_code

Topic: approximation   Node: fec110557381

Provenance: helper lemma. Input/output encoding, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)); a standard prefix-free binary code of rationals built on nat_self_delimiting_code.

The binary word encoding a rational number q: the bit true if q < 0 and false otherwise, followed by the self-delimiting code nat_self_delimiting_code of the absolute value of the numerator of q in lowest terms, followed by the self-delimiting code of the (positive) denominator of q in lowest terms.
-/

/-- The self-delimiting binary code of a rational number: a sign bit, then the absolute value of the numerator and the denominator (lowest terms) each in `nat_self_delimiting_code`. -/
def rat_self_delimiting_code (q : ℚ) : List Bool :=
  [decide (q < 0)] ++ nat_self_delimiting_code q.num.natAbs ++ nat_self_delimiting_code q.den
