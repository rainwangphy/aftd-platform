import AFTD.Prelude

/-!
# lowMul3Target1

Topic: circuits   Node: 205db5c99ed2

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 2 (Targets)

The target function z_1 : (Fin 6 → Bool) → ZMod 2 of the 3-bit low-half multiplier, given by z_1(x) = a_0 * b_1 + a_1 * b_0 = x(0) * x(4) + x(1) * x(3).
-/

/-- The second output bit z_1 = a_0 * b_1 + a_1 * b_0 of the three-bit low-half multiplier. -/
def lowMul3Target1 : (Fin 6 → Bool) → ZMod 2 := (fun x => if x 0 then (1 : ZMod 2) else 0) * (fun x => if x 4 then 1 else 0) +
   (fun x => if x 1 then 1 else 0) * (fun x => if x 3 then 1 else 0)
