import AFTD.Prelude

/-!
# binary_form_compression_bound

Topic: elementary_number_theory   Node: 820f4292bf7c

Provenance: formalization of a published result. Source: arXiv:2611.02063 Lemma 3.1

The compression bound $h_a(k)$ is defined for natural numbers $a$ and $k$ by $h_a(0) = 1$, and $h_a(k) = 2 \sum_{j=0}^{a-1} \binom{k-1}{j}$ for $k \ge 1$.
-/

/-- Compression bound h_a(k) for binary linear forms modulo 2^a in dimension k + 1. -/
def binary_form_compression_bound (a k : ℕ) : ℕ := if k = 0 then 1 else 2 * ∑ j ∈ Finset.range a, Nat.choose (k - 1) j
