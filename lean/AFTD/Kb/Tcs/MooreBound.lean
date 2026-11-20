import AFTD.Prelude

/-!
# moore_bound

Topic: graphs   Node: a058b4cbc606

Provenance: formalization of a published result. Source: arXiv:2611.26037 Sec. 1

The Moore bound m(d, k) is defined as 1 + d * ∑_{i=0}^{k-1} (d-1)^i, representing the maximum possible number of vertices in a graph of maximum degree at most d and diameter at most k.
-/

/-- The Moore bound m(d, k) = 1 + d * ∑_{i=0}^{k-1} (d-1)^i on the order of a graph of maximum degree d and diameter at most k. -/
def moore_bound (d k : ℕ) : ℕ := 1 + d * ∑ i ∈ Finset.range k, (d - 1) ^ i
