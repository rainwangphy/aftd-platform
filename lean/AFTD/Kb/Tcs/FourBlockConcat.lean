import AFTD.Prelude

/-!
# four_block_concat

Topic: information   Node: 69f548c9ba0a

Provenance: formalization of a published result. Source: arXiv:2610.29807, Section 2.3

The four-block concatenation four_block_concat of four Boolean functions f0, f1, f2, f3 : (Fin m → ZMod 2) → ZMod 2 is the Boolean function on Fin (m + 2) → ZMod 2 that sends v to (1 + y1) * (1 + y2) * f0 x + y1 * (1 + y2) * f1 x + (1 + y1) * y2 * f2 x + y1 * y2 * f3 x, where x = fun i => v (Fin.castAdd 2 i), y1 = v (Fin.natAdd m 0), and y2 = v (Fin.natAdd m 1).
-/

/-- Four-block concatenation of m-variable Boolean functions with block order 00, 10, 01, 11 into an (m+2)-variable Boolean function. -/
def four_block_concat {m : ℕ} (f0 f1 f2 f3 : (Fin m → ZMod 2) → ZMod 2) :
    (Fin (m + 2) → ZMod 2) → ZMod 2 := fun v =>
  let x : Fin m → ZMod 2 := fun i => v (Fin.castAdd 2 i)
  let y1 : ZMod 2 := v (Fin.natAdd m 0)
  let y2 : ZMod 2 := v (Fin.natAdd m 1)
  (1 + y1) * (1 + y2) * f0 x + y1 * (1 + y2) * f1 x + (1 + y1) * y2 * f2 x + y1 * y2 * f3 x
