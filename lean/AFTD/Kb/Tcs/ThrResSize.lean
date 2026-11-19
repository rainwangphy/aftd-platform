import AFTD.Prelude
import AFTD.Kb.Tcs.ThrCond
import AFTD.Kb.Tcs.ThrCondUnarySize

/-!
# thr_res_size

Topic: proof_complexity   Node: 61129fed2b42

Provenance: formalization of a published result. Source: arXiv:2611.24548 Section 2.1, Definition 2.12

The unary size of a Threshold Resolution proof π, equal to the number of lines plus the sum of the unary sizes of its lines.
-/

/-- Unary size of a Thr-Res proof: number of lines plus sum of unary sizes of the lines. -/
def thr_res_size {n : ℕ} (π : List (ThrCond n)) : ℕ :=
  π.length + (π.map thr_cond_unary_size).sum
