import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfLitDecidableEq
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_clause_to_lin

Topic: proof_complexity   Node: 24627efe1852

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 4.1

The linear inequality embedding of a CNF clause C over n variables, asserting ∑_{l ∈ C} [l] ≥ 1 where [x_i] = x_i and [~x_i] = 1 - x_i.
-/

/-- The embedding of a CNF clause as a linear inequality asserting that the sum of its literals is at least 1. -/
def cnf_clause_to_lin (n : ℕ) (C : Finset (CnfLit (Fin n))) : LinIneq n :=
  ⟨fun j => (if CnfLit.pos j ∈ C then 1 else 0) - (if CnfLit.neg j ∈ C then 1 else 0),
   1 - ∑ j : Fin n, (if CnfLit.neg j ∈ C then (1 : ℤ) else 0)⟩
