import AFTD.Prelude

/-!
# graph_11

Topic: graphs   Node: facb79573efe

Provenance: formalization of a published result. Source: arXiv:2610.39430 Definition 3.1

The 11-vertex simple graph G_11 on Fin 11 consisting of a base 4-cycle 0-1-2-3-0, four caps 4, 5, 6, 7 adjacent to consecutive base pairs, two links 8 and 9 adjacent to pairs of caps (4,6) and (5,7) respectively, and a hub 10 adjacent to all four caps and both links.
-/

/-- The 11-vertex simple graph G_11 with base cycle, four caps, two links and a hub. -/
def graph_11 : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun u v =>
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
  (u = 4 ∧ (v = 0 ∨ v = 1)) ∨
  (u = 5 ∧ (v = 1 ∨ v = 2)) ∨
  (u = 6 ∧ (v = 2 ∨ v = 3)) ∨
  (u = 7 ∧ (v = 3 ∨ v = 0)) ∨
  (u = 8 ∧ (v = 4 ∨ v = 6)) ∨
  (u = 9 ∧ (v = 5 ∨ v = 7)) ∨
  (u = 10 ∧ (v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9))
