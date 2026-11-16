import AFTD.Prelude

/-!
# lowMul3Target2

Topic: circuits   Node: 046f3b016cf9

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 2 (Targets)

The target function z_2 : (Fin 6 → Bool) → ZMod 2 of the 3-bit low-half multiplier, given by z_2(x) = x(0)*x(5) + x(1)*x(4) + x(2)*x(3) + x(0)*x(1)*x(3)*x(4).
-/

/-- The third output bit z_2 = q_2 + a_0 * a_1 * b_0 * b_1 of the three-bit low-half multiplier. -/
def lowMul3Target2 : (Fin 6 → Bool) → ZMod 2 := (fun x => if x 0 then (1 : ZMod 2) else 0) * (fun x => if x 5 then 1 else 0) +
   (fun x => if x 1 then 1 else 0) * (fun x => if x 4 then 1 else 0) +
   (fun x => if x 2 then 1 else 0) * (fun x => if x 3 then 1 else 0) +
   (fun x => if x 0 then 1 else 0) * (fun x => if x 1 then 1 else 0) *
     (fun x => if x 3 then 1 else 0) * (fun x => if x 4 then 1 else 0)
