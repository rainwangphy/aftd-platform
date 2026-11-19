import AFTD.Prelude
import AFTD.Kb.Tcs.ThrCond
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfLit

/-!
# thr_to_lin

Topic: proof_complexity   Node: a41689f1aaef

Provenance: formalization of a published result. Source: arXiv:2611.24548 Section 4.1

The translation ⟨f ≥ s⟩ of a threshold condition to a linear inequality over plain Boolean variables, obtained by substituting ~x_i = 1 - x_i.
-/

/-- The translation ⟨f ≥ s⟩ of a threshold condition to a linear inequality by replacing ~x_i with 1 - x_i. -/
def thr_to_lin {n : ℕ} (T : ThrCond n) : LinIneq n :=
  ⟨fun i => (T.coeffs (CnfLit.pos i) : ℤ) - (T.coeffs (CnfLit.neg i) : ℤ),
   T.threshold - ∑ i : Fin n, (T.coeffs (CnfLit.neg i) : ℤ)⟩
