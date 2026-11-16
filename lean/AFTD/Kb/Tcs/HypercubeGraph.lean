import AFTD.Prelude

/-!
# hypercube_graph

Topic: combinatorics   Node: 7f3a9f578d2a

Provenance: formalization of a published result. Source: arXiv:2611.16243 Section 1

The n-dimensional hypercube graph Q_n has vertex set {0, 1}^n, with two vertices adjacent if and only if their Hamming distance is 1 (they differ in exactly one coordinate).
-/

/-- The n-dimensional hypercube graph Q_n on {0, 1}^n with edges between vertices at Hamming distance 1. -/
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := hammingDist u v = 1
  symm := ⟨by intro u v h; rw [hammingDist_comm]; exact h⟩
  loopless := ⟨by intro u h; rw [hammingDist_self] at h; contradiction⟩
