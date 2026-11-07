import AFTD.Prelude

/-!
# online_carpool_orientations

Topic: online_algorithms   Node: 06a1a995f0cc

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 1.1, Online carpooling against an oblivious adversary

For an instance on vertex set Fin n and a random tape r of K boolean coins, given an orientation function orient that takes an edge history in List (Fin n × Fin n) and the coins in Fin K → Bool to an orientation bit in Bool, online_carpool_orientations n orient edges r is the list of boolean orientations for the edges in edges, where the i-th edge is oriented using orient applied to the prefix edges.take (i + 1) and r.
-/

/-- The list of boolean orientations produced by an online carpooling algorithm given edge history on Fin n and random coins. -/
def online_carpool_orientations (n : ℕ) {K : ℕ}
    (orient : List (Fin n × Fin n) → (Fin K → Bool) → Bool)
    (edges : List (Fin n × Fin n)) (r : Fin K → Bool) : List Bool := List.ofFn (fun i : Fin edges.length => orient (edges.take (i.val + 1)) r)
