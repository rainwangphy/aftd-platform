import AFTD.Prelude

/-!
# hamming_close_skew_system

Topic: combinatorics   Node: 1c20af28eee4

Provenance: formalization of a published result. Source: arXiv:2611.20820 Sec. 5.7

A pair of sequences of k points (v, w) in the n-dimensional Hamming space {0,1}^n forms a close-skew system of radius r if all pairs v_i, v_j are at Hamming distance at most r, each w_i is at Hamming distance at least r + 1 from v_i, and each w_i is at Hamming distance at most r from v_j for all j < i.
-/

/-- A close-skew system of radius r in the Hamming space {0,1}^n is a pair of sequences (v, w) of points in Fin n -> Bool where the v_i are pairwise r-close, each w_i is at distance at least r + 1 from v_i, and each w_i is at distance at most r from v_j for j < i. -/
def hamming_close_skew_system {n : ℕ} (r : ℕ) {k : ℕ} (v w : Fin k → Fin n → Bool) : Prop :=
  (∀ i j : Fin k, hammingDist (v i) (v j) ≤ r) ∧
  (∀ i : Fin k, r + 1 ≤ hammingDist (w i) (v i)) ∧
  (∀ i j : Fin k, j < i → hammingDist (w i) (v j) ≤ r)
