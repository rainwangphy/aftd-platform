import AFTD.Prelude

/-!
# SevenArc

Topic: submodular   Node: 7be25f1eb28d

Provenance: formalization of a published result. Source: arXiv:2611.23244 Equation (19)

The nine directed arcs of the seven-vertex graph: arborescence arcs (s,u), (u,v), (v,w), (v,t_1), (w,t_2), (w,t_3) and shortcut arcs (s,t_1), (s,t_2), (u,t_3).
-/

/-- The nine directed arcs of the seven-vertex topology for the single-source unsplittable flow counterexample. -/
inductive SevenArc : Type | su | uv | vw | vt1 | wt2 | wt3 | st1 | st2 | ut3
  deriving DecidableEq
