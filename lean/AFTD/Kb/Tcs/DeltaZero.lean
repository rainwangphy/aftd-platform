import AFTD.Prelude

/-!
# delta_zero

Topic: quantum   Node: 76a158adc37c

Provenance: formalization of a published result. Source: arXiv:2610.09341, Lemma A.4

For a natural number s, delta_zero s is the function from (Fin s → ZMod 2) to ZMod 2 that evaluates to 1 in ZMod 2 at 0 and to 0 in ZMod 2 elsewhere.
-/

open scoped Classical in
/-- The indicator of the origin in (Fin s → ZMod 2). -/
def delta_zero (s : ℕ) : (Fin s → ZMod 2) → ZMod 2 := fun β => if β = 0 then 1 else 0
