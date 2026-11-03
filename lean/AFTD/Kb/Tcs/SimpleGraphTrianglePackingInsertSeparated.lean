import AFTD.Prelude

/-!
# simple_graph_triangle_packing_insert_separated

Topic: graphs   Node: 5b8bc6c3fbd0

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

A triangle sharing at most one vertex with every member of an edge-disjoint triangle packing can be inserted, increasing the packing size by one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_packing_insert_separated
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finset (Finset V)) (t : Finset V)
    (hp : ∀ s ∈ P, G.IsNClique 3 s)
    (hpp : (P : Set (Finset V)).Pairwise (fun s r => (s ∩ r).card ≤ 1))
    (ht : G.IsNClique 3 t)
    (hsep : ∀ s ∈ P, (s ∩ t).card ≤ 1) :
    (∀ s ∈ insert t P, G.IsNClique 3 s) ∧
    ((insert t P : Finset (Finset V)) : Set (Finset V)).Pairwise
      (fun s r => (s ∩ r).card ≤ 1) ∧
    (insert t P).card = P.card + 1 := by
  classical
  have hnot : t ∉ P := by
    intro h
    have hh := hsep t h
    rw [Finset.inter_self, ht.card_eq] at hh
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ht
    · exact hp s hs
  · rw [Finset.coe_insert]
    refine hpp.insert ?_
    intro s hs _
    have hh := hsep s hs
    exact ⟨by rw [Finset.inter_comm]; exact hh, hh⟩
  · simp [hnot, Nat.add_comm]
