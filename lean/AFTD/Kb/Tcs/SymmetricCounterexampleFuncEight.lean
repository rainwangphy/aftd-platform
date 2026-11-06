import AFTD.Prelude

/-!
# symmetric_counterexample_func_eight

Topic: combinatorics   Node: dfd0e6604962

Provenance: formalization of a published result. Source: arXiv:2611.06744 Theorem 1 and Section 4

The eight-variable symmetric Boolean function F_8 = 1 + σ_2 + σ_4 on (Fin 8 → ZMod 2), defined as the sum modulo two of 1 and the elementary symmetric Boolean polynomials of degrees 2 and 4.
-/

/-- The eight-variable symmetric Boolean function F_8 = 1 + σ_2 + σ_4. -/
def symmetric_counterexample_func_eight (x : Fin 8 → ZMod 2) : ZMod 2 :=
  1 + (∑ s ∈ Finset.powersetCard 2 Finset.univ, ∏ i ∈ s, x i) +
      (∑ s ∈ Finset.powersetCard 4 Finset.univ, ∏ i ∈ s, x i)
