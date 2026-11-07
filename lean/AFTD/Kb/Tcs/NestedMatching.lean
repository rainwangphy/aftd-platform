import AFTD.Prelude

/-!
# nested_matching

Topic: graphs   Node: f2267f35f671

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 1

The nested matching NM_{2k} is the cyclically ordered simple graph on 2k vertices with edges {i, 2k - 1 - i} for 0 ≤ i < k.
-/

/-- The cyclically ordered nested matching on 2k vertices. -/
def nested_matching (k : ℕ) : SimpleGraph (Fin (2 * k)) := SimpleGraph.fromRel fun u v => u.val + v.val + 1 = 2 * k
