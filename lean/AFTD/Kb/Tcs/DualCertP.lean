import AFTD.Prelude
import AFTD.Kb.Tcs.TriangularNumber

/-!
# dual_cert_p

Topic: combinatorics   Node: b082a6f583e1

Provenance: formalization of a published result. Source: arXiv:2611.17360 line 121

For each natural number m, p(m) is the largest integer p >= 2 such that p + (p-2)(p-1)/2 < m, or 1 if no such integer exists.
-/

/-- The integer p(m) used in the signed relation for gap m. -/
def dual_cert_p (m : ℕ) : ℕ :=
  let s := (Finset.Icc 2 m).filter (fun p => p + triangular_number (p - 2) < m)
  if h : s.Nonempty then s.max' h else 1
