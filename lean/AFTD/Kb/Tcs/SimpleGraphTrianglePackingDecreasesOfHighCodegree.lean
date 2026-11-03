import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphMaximalPackingCommonNeighborsLe

/-!
# simple_graph_triangle_packing_decreases_of_high_codegree

Topic: graphs   Node: ab4a1e5f325d

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

Deleting an edge with more than twice the maximum triangle packing number common neighbors strictly decreases the packing number.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_packing_decreases_of_high_codegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : G.Adj u v)
    (hlarge : 2 * simple_graph_triangle_packing_number G <
      ((Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)).card) :
    simple_graph_triangle_packing_number (G.deleteEdges {s(u,v)}) < simple_graph_triangle_packing_number G := by
  classical
  let H := G.deleteEdges {s(u,v)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le (G := G) {s(u,v)}
  have hle : simple_graph_triangle_packing_number H ≤ simple_graph_triangle_packing_number G :=
    simple_graph_triangle_packing_number_mono G H hHG
  by_contra hn
  change ¬ simple_graph_triangle_packing_number H < simple_graph_triangle_packing_number G at hn
  have heq : simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G := by omega
  let A : Set ℕ := {n | ∃ P : Finset (Finset V), (∀ t ∈ P, H.IsNClique 3 t) ∧
    (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ P.card = n}
  have hne : A.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hbdd : BddAbove A := by
    refine ⟨Fintype.card (Finset V), ?_⟩
    rintro n ⟨P, _, _, rfl⟩
    exact Finset.card_le_univ P
  obtain ⟨P, hPH, hpair, hcard⟩ := Nat.sSup_mem hne hbdd
  have hcard' : P.card = simple_graph_triangle_packing_number G := by
    change P.card = simple_graph_triangle_packing_number H at hcard
    omega
  have hPG : ∀ t ∈ P, G.IsNClique 3 t := by
    intro t ht
    exact (hPH t ht).mono hHG
  have hmax := simple_graph_maximum_triangle_packing_edge_meets G P hPG hpair hcard'
  have havoid : ∀ s ∈ P, ¬(u ∈ s ∧ v ∈ s) := by
    intro s hs hmem
    have hadj : H.Adj u v := (hPH s hs).isClique hmem.1 hmem.2 (G.ne_of_adj huv)
    have := (SimpleGraph.deleteEdges_adj.mp hadj).2
    exact this (by simp)
  have hsmall := simple_graph_maximal_packing_common_neighbors_le G u v P huv hPG hmax havoid
  rw [hcard'] at hsmall
  omega
