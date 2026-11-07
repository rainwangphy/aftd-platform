import AFTD.Prelude

/-!
# monotone_path

Topic: graphs   Node: 1f12bd51bca2

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 1

The monotone path MP_l is the cyclically ordered simple graph on l vertices with edges between consecutive vertices i and i + 1 for 0 ≤ i < l - 1.
-/

/-- The cyclically ordered monotone path on l vertices. -/
def monotone_path (l : ℕ) : SimpleGraph (Fin l) := SimpleGraph.fromRel fun u v => u.val + 1 = v.val
