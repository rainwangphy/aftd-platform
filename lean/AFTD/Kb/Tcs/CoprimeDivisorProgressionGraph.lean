import AFTD.Prelude

/-!
# coprime_divisor_progression_graph

Topic: graphs   Node: 8dcb01268fb4

Provenance: formalization of a published result. Source: arXiv:2610.37512

For a natural number n and integers a and b, the coprime divisor progression graph is the bipartite simple graph on the disjoint union of the positive divisors of n and the set of integers in the arithmetic progression image {a + bt : t ∈ {0, ..., |D(n)| - 1}}, with an edge between a divisor d and a progression term x if and only if d and x are coprime in ℤ.
-/

/-- The bipartite simple graph on D(n) and the progression image set {a + bt : 0 ≤ t < |D(n)|} with edges for coprimality. -/
def coprime_divisor_progression_graph (n : ℕ) (a b : ℤ) :
    SimpleGraph ({ d : ℕ // d ∈ Nat.divisors n } ⊕ { x : ℤ // x ∈ (Finset.range (Nat.divisors n).card).image (fun (t : ℕ) => a + b * (t : ℤ)) }) := SimpleGraph.fromRel fun u v =>
    match u, v with
    | Sum.inl d, Sum.inr x => IsCoprime (d.1 : ℤ) x.1
    | _, _ => False
