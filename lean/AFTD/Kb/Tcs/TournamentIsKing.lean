import AFTD.Prelude

/-!
# tournament_is_king

Topic: graphs   Node: 689227a2408c

Provenance: formalization of a published result. Source: arXiv:2610.40521 Section 1

A vertex v in a tournament T is a king if every other vertex u is reachable from v in at most two steps: either there is an arc from v to u, or there is a vertex w with arcs from v to w and from w to u.
-/

/-- A vertex v in a tournament T is a king if every other vertex is reachable from v by a directed path of length at most two. -/
def tournament_is_king {V : Type*} (T : Digraph V) (v : V) : Prop := ∀ u, u ≠ v → T.Adj v u ∨ ∃ w, T.Adj v w ∧ T.Adj w u
