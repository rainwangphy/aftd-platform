import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges
import AFTD.Kb.Tcs.Op874pfMissing
import AFTD.Kb.Tcs.Op874pfColor
import AFTD.Kb.Tcs.Op874pfInducedEdges

/-!
# op874_pseudoforest_pairrich_data

Topic: graphs   Node: 38174ec5ff4f

Provenance: helper lemma. OP-874: finite data for the fixed-color pseudoforest obstruction.

In the explicit eight-vertex graph, the displayed edge colors are proper, the listed missing colors are exactly their complements, adjacent missing palettes intersect in at most two colors, and every vertex subset of every missing-color induced graph spans at most as many edges as vertices.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem op874_pseudoforest_pairrich_data :
    (∀ v : Fin 8, (op874pf_missing v).card = 3) ∧
    (∀ v z, z ∈ op874pf_missing v ↔
      ∀ w : Fin 8, s(v,w) ∈ op874pf_edges → op874pf_color s(v,w) ≠ z) ∧
    (∀ u v w : Fin 8, u ≠ w → s(u,v) ∈ op874pf_edges → s(v,w) ∈ op874pf_edges →
      op874pf_color s(u,v) ≠ op874pf_color s(v,w)) ∧
    (∀ u v : Fin 8, s(u,v) ∈ op874pf_edges →
      (op874pf_missing u ∩ op874pf_missing v).card ≤ 2) ∧
    (∀ z : Fin 6, ∀ S : Finset (Fin 8),
      (∀ v ∈ S, z ∈ op874pf_missing v) → (op874pf_induced_edges S).card ≤ S.card) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro z
  fin_cases z <;> decide
