import AFTD.Prelude
import AFTD.Kb.Tcs.CampbellHowardConditions
import AFTD.Kb.Tcs.CssZDistanceGeThree

/-!
# css_quasi_transversal_ccz_code

Topic: quantum   Node: a9f0c1f8b779

Provenance: formalization of a published result. Source: arXiv:2610.09341 Thm 3.3

A CSS quantum code of block length n specified by a 3 by n logical X-operator matrix K and an s by n X-stabilizer matrix S over ZMod 2 has quasi-transversal CCZ if it has Z-distance at least 3 and satisfies the nine Campbell-Howard conditions.
-/

/-- A CSS code has quasi-transversal CCZ if it has Z-distance at least 3 and satisfies the nine Campbell-Howard conditions. -/
def css_quasi_transversal_ccz_code (n s : ℕ)
    (K : Matrix (Fin 3) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2)) : Prop :=
  css_z_distance_ge_three K S ∧ campbell_howard_conditions K S
