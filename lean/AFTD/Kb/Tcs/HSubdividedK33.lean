import AFTD.Prelude

/-!
# h_subdivided_k33

Topic: graphs   Node: 7b9fbc84c9a2

Provenance: formalization of a published result. Source: arXiv:2610.32404, Section 11

The 7-vertex graph obtained by subdividing one edge of the complete bipartite graph K_{3,3} exactly once.
-/

/-- The 7-vertex graph H obtained from K_{3,3} by subdividing one edge once. -/
def h_subdivided_k33 : SimpleGraph (Fin 7) := SimpleGraph.fromRel (fun u v =>
    (u = 0 ∧ v = 6) ∨ (u = 6 ∧ v = 0) ∨
    (u = 6 ∧ v = 3) ∨ (u = 3 ∧ v = 6) ∨
    (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨
    (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0) ∨
    (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) ∨
    (u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1) ∨
    (u = 1 ∧ v = 5) ∨ (u = 5 ∧ v = 1) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨
    (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2) ∨
    (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2))
