import AFTD.Prelude

/-!
# StandardExample

Topic: combinatorics   Node: da22cb539b5d

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

The standard example S_k of order k is a type with k minimal elements and k maximal elements.
-/

/-- The standard example of order k as a bipartite type with k minimal and k maximal elements. -/
inductive StandardExample (k : ℕ) : Type | min (i : Fin k) : StandardExample k
| max (j : Fin k) : StandardExample k
