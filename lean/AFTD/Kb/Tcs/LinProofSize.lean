import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.LinIneqUnarySize

/-!
# lin_proof_size

Topic: proof_complexity   Node: da7d65e672da

Provenance: formalization of a published result. Source: arXiv:2611.24548 Section 2.1, Definition 4.1

The unary size of a linear inequality proof π, equal to the number of lines plus the sum of the unary sizes of its lines.
-/

/-- Unary size of a linear inequality proof: number of lines plus sum of unary sizes. -/
def lin_proof_size {n : ℕ} (π : List (LinIneq n)) : ℕ :=
  π.length + (π.map lin_ineq_unary_size).sum
