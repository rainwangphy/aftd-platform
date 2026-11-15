import AFTD.Prelude

/-!
# noon_realign_witness

Topic: quantum_mechanics   Node: 55ddbddaf5a5

Provenance: formalization of a published result. Source: arXiv:2611.17021

For any natural number N, real balance parameter q, and real transmissivities x, y, the second-moment realignment witness W_N(q, x, y) is defined as the sum over k in Finset.range (N + 1) of (q * (Nat.choose N k : Real) * x^k * (1-x)^(N-k) + (1-q) * (Nat.choose N k : Real) * y^k * (1-y)^(N-k))^2 plus 4 * q * (1-q) * (x * y)^N.
-/

/-- The second-moment realignment entanglement witness polynomial W_N(q, x, y) for a two-mode generalized NOON state. -/
def noon_realign_witness (N : ℕ) (q x y : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (N + 1),
    (q * (Nat.choose N k : ℝ) * x ^ k * (1 - x) ^ (N - k) +
     (1 - q) * (Nat.choose N k : ℝ) * y ^ k * (1 - y) ^ (N - k)) ^ 2) +
  4 * q * (1 - q) * (x * y) ^ N
