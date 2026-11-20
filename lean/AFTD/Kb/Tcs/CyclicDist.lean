import AFTD.Prelude

/-!
# cyclic_dist

Topic: graphs   Node: dbe7ec6881ea

Provenance: formalization of a published result. Source: scout/2611-22830-independent-sets-in-the-2-token-graph-of-a-cycle-and-kings.md:159

The cyclic distance between two vertices u and v of the n-cycle is the minimum of (u - v) mod n and (v - u) mod n.
-/

/-- Cyclic distance between two vertices in the cycle graph of order n. -/
def cyclic_dist (n : ℕ) (u v : Fin n) : ℕ := min (u - v).val (n - (u - v).val)
