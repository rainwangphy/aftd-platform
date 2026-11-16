import AFTD.Prelude

/-!
# low_half_mul3_bit

Topic: circuits   Node: bcafbb34b8c1

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 1

The function taking index k : Fin 3 and vector v : Fin 6 → ZMod 2 and returning the element of ZMod 2 obtained by computing the product (a * b) % 8 where a = (v 0).val + 2 * (v 1).val + 4 * (v 2).val and b = (v 3).val + 2 * (v 4).val + 4 * (v 5).val, taking the k-th bit (prod / 2 ^ k.val) % 2, and coercing to ZMod 2.
-/

/-- The k-th bit in ZMod 2 of the 3-bit low-half integer multiplication modulo 8. -/
def low_half_mul3_bit (k : Fin 3) (v : Fin 6 → ZMod 2) : ZMod 2 :=
  let a := (v 0).val + 2 * (v 1).val + 4 * (v 2).val
  let b := (v 3).val + 2 * (v 4).val + 4 * (v 5).val
  let prod := (a * b) % 8
  ((prod / 2 ^ k.val) % 2 : ℕ)
