import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_maximum_triangle_packing_edge_meets

Topic: graphs   Node: 8441287daf3b

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

Every triangle shares an edge with a member of a maximum edge-disjoint triangle packing.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_maximum_triangle_packing_edge_meets
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finset (Finset V))
    (hcl : ∀ t ∈ P, G.IsNClique 3 t)
    (hpair : (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (hsize : P.card = simple_graph_triangle_packing_number G) :
    ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card := by
  classical
  intro t ht
  by_contra hno
  push_neg at hno
  have htP : t ∉ P := by
    intro htP
    have h := hno t htP
    rw [Finset.inter_self, ht.card_eq] at h
    omega
  have hp1 : ∀ s ∈ insert t P, G.IsNClique 3 s := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ht
    · exact hcl s hs
  have hp2 : ((insert t P : Finset (Finset V)) : Set (Finset V)).Pairwise
      (fun s t => (s ∩ t).card ≤ 1) := by
    rw [Finset.coe_insert]
    refine hpair.insert ?_
    intro s hs _
    have h := hno s hs
    exact ⟨by rw [Finset.inter_comm]; omega, by omega⟩
  let A : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ a ∈ T, G.IsNClique 3 a) ∧
      (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n}
  have hbound : BddAbove A := by
    refine ⟨Fintype.card (Finset V), ?_⟩
    rintro n ⟨T, _, _, rfl⟩
    exact Finset.card_le_univ T
  have hins : (insert t P).card ≤ simple_graph_triangle_packing_number G := by
    exact le_csSup hbound ⟨insert t P, hp1, hp2, rfl⟩
  rw [Finset.card_insert_of_notMem htP, hsize] at hins
  omega
