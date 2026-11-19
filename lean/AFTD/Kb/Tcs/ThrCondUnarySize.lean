import AFTD.Prelude
import AFTD.Kb.Tcs.ThrCond
import AFTD.Kb.Tcs.CnfLit

/-!
# thr_cond_unary_size

Topic: proof_complexity   Node: 564790193486

Provenance: formalization of a published result. Source: arXiv:2611.24548 Section 2.1, Definition 2.12

The unary size of a threshold condition f ≥ s, defined as the sum of all literal multiplicities plus |s| + 1.
-/

/-- Unary size of a threshold condition f ≥ s: sum of literal multiplicities plus |s| + 1. -/
def thr_cond_unary_size {n : ℕ} (T : ThrCond n) : ℕ :=
  (∑ i : Fin n, T.coeffs (CnfLit.pos i)) + (∑ i : Fin n, T.coeffs (CnfLit.neg i)) + T.threshold.natAbs + 1
