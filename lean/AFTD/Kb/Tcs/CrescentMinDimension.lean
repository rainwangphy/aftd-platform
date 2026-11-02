import AFTD.Prelude
import AFTD.Kb.Tcs.IsCrescentConfiguration

/-!
# crescent_min_dimension

Topic: combinatorics   Node: 7c436810375d

Provenance: formalization of a published result. Source: arXiv:2610.38368, Section 1

The minimum dimension D(n) is the least integer d ≥ 2 such that there exists an n-point crescent configuration in ℝ^d.
-/

/-- The minimum dimension D(n) in which an n-point crescent configuration exists. -/
noncomputable def crescent_min_dimension (n : ℕ) : ℕ :=
  sInf {d : ℕ | 2 ≤ d ∧ ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧ is_crescent_configuration S}
