import AFTD.Prelude

/-!
# lowMul3Target0

Topic: circuits   Node: d2813bddc1e1

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 2 (Targets)

The target function z_0 : (Fin 6 → Bool) → ZMod 2 of the 3-bit low-half multiplier, given by z_0(x) = a_0 * b_0 = x(0) * x(3).
-/

/-- The first output bit z_0 = a_0 * b_0 of the three-bit low-half multiplier. -/
def lowMul3Target0 : (Fin 6 → Bool) → ZMod 2 := (fun x => if x 0 then (1 : ZMod 2) else 0) * (fun x => if x 3 then 1 else 0)
