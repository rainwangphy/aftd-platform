import AFTD.Prelude

/-!
# icosahedron_graph

Topic: graphs   Node: 0a86085d3a63

Provenance: formalization of a published result. Source: arXiv:2610.36620, Section 3.1

The simple graph on Fin 12 defined via SimpleGraph.fromRel with antipodal vertices 0 and 11: vertex 0 is adjacent to vertices 1 through 5, vertex 11 is adjacent to vertices 6 through 10, the vertices 1 through 5 form a 5-cycle with edges between x and x % 5 + 1, the vertices 6 through 10 form a 5-cycle with edges between y and 6 + (y - 6 + 1) % 5, and each vertex x in {1, ..., 5} is connected to vertices 6 + (x - 1) and 6 + (x - 1 + 4) % 5 in {6, ..., 10}.
-/

/-- The icosahedron graph on Fin 12 with antipodal vertices 0 and 11. -/
def icosahedron_graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel (fun u v : Fin 12 =>
  let x := u.val
  let y := v.val
  (x = 0 ∧ 1 ≤ y ∧ y ≤ 5) ∨
  (x = 11 ∧ 6 ≤ y ∧ y ≤ 10) ∨
  (1 ≤ x ∧ x ≤ 5 ∧ 1 ≤ y ∧ y ≤ 5 ∧ (y = x % 5 + 1 ∨ x = y % 5 + 1)) ∨
  (6 ≤ x ∧ x ≤ 10 ∧ 6 ≤ y ∧ y ≤ 10 ∧ (y = 6 + (x - 6 + 1) % 5 ∨ x = 6 + (y - 6 + 1) % 5)) ∨
  (1 ≤ x ∧ x ≤ 5 ∧ 6 ≤ y ∧ y ≤ 10 ∧ (y = 6 + (x - 1) ∨ y = 6 + (x - 1 + 4) % 5)))
