import AFTD.Prelude

/-!
# sixteen_spin_weight

Topic: quantum_mechanics   Node: 64b73731b148

Provenance: formalization of a published result. Source: OP-1695; arXiv:2610.27080

For a real angle θ and a difference vector d in (Fin 2)^4, the sixteen-spin edge weight w(d) is exp(8 i θ) if d = (0, 1, 0, 1), exp(-8 i θ) if d = (1, 1, 0, 1), and 1 otherwise.
-/

/-- Weight w_e(d) of a spin difference d in (Fin 2)^4 on edge e with angle θ_e. -/
noncomputable def sixteen_spin_weight (θ : ℝ) (d : Fin 4 → Fin 2) : ℂ := if d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0 ∧ d 3 = 1 then Complex.exp (8 * Complex.I * θ)
  else if d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0 ∧ d 3 = 1 then Complex.exp (-8 * Complex.I * θ)
  else 1
