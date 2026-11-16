import AFTD.Prelude

/-!
# low_half_mul3_six_and_circuit

Topic: circuits   Node: 6badefc0edc3

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 3

The function taking vector v : Fin 6 → ZMod 2 and index k : Fin 3 and returning an element of ZMod 2 computed from six AND gates over ZMod 2: g0 = v 0 * v 3, g1 = v 0 * v 4, g2 = v 1 * v 3, g3 = v 0 * v 5, g4 = v 2 * v 3, and g5 = (g1 + v 1) * (g2 + v 4), returning g0 for k = 0, g1 + g2 for k = 1, and g5 + g1 + g2 + g3 + g4 for k = 2.
-/

/-- The six-AND circuit for 3-bit low-half multiplication from arXiv:2611.15992 Section 3. -/
def low_half_mul3_six_and_circuit (v : Fin 6 → ZMod 2) (k : Fin 3) : ZMod 2 :=
  let g0 := v 0 * v 3
  let g1 := v 0 * v 4
  let g2 := v 1 * v 3
  let g3 := v 0 * v 5
  let g4 := v 2 * v 3
  let g5 := (g1 + v 1) * (g2 + v 4)
  match k with
  | 0 => g0
  | 1 => g1 + g2
  | 2 => g5 + g1 + g2 + g3 + g4
