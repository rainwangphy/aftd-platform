import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis

/-!
# xz_pauli

Topic: quantum_mechanics   Node: 21e7e8843e53

Provenance: formalization of a published result. Source: arXiv:2610.20846, Appendix C

The function `xz_pauli : Fin 2 → Fin 2 → PauliBasis` taking two curried arguments a, b : Fin 2, mapping a = 0, b = 0 to PauliBasis.X; a = 0, b = 1 to PauliBasis.Y; a = 1, b = 0 to PauliBasis.I; and a = 1, b = 1 to PauliBasis.Z.
-/

/-- The single-qubit Pauli basis assignment M_(a,b) sending (0,0) to X, (0,1) to Y, (1,0) to I, and (1,1) to Z. -/
def xz_pauli (a b : Fin 2) : PauliBasis := if a.val = 0 then
    if b.val = 0 then PauliBasis.X else PauliBasis.Y
  else
    if b.val = 0 then PauliBasis.I else PauliBasis.Z
