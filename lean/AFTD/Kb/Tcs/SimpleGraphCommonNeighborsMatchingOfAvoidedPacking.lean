import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetRankTwoCoverMatchingBound
import AFTD.Kb.Tcs.SimpleGraphCommonNeighborMeetsPackingStar

/-!
# simple_graph_common_neighbors_matching_of_avoided_packing

Topic: graphs   Node: 588b05ff4346

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign, related to matching-cover reductions in https://arxiv.org/abs/2610.15269; see state/campaigns/triangle_reductions/high_codegree_route_in512.md.

For a triangle-maximal family of size p avoiding an edge with d common neighbors, their induced graph contains a matching of size at least d minus p.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_common_neighbors_matching_of_avoided_packing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (P : Finset (Finset V)) (huv : G.Adj u v)
    (hcl : ∀ t ∈ P, G.IsNClique 3 t)
    (hmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card)
    (havoid : ∀ s ∈ P, ¬(u ∈ s ∧ v ∈ s)) :
    ∃ M : Finset (Finset V),
      (M : Set (Finset V)).Pairwise Disjoint ∧
      (∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj u x ∧ G.Adj v x) ∧
        (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y)) ∧
      ((Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)).card ≤ P.card + M.card := by
  classical
  let N : Finset V := (Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)
  let F (s : Finset V) : Finset V :=
    if u ∈ s then (s.erase u).filter (fun x => x ∈ N)
    else if v ∈ s then (s.erase v).filter (fun x => x ∈ N) else ∅
  let B : Finset (Finset V) := P.image F
  have hFsub : ∀ s, F s ⊆ s := by
    intro s
    by_cases hu : u ∈ s
    · simp only [F, hu, ↓reduceIte]
      exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    · by_cases hv : v ∈ s
      · simp only [F, hu, hv, ↓reduceIte]
        exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      · simp [F, hu, hv]
  have hFN : ∀ s, F s ⊆ N := by
    intro s
    by_cases hu : u ∈ s
    · simp only [F, hu, ↓reduceIte]
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    · by_cases hv : v ∈ s
      · simp only [F, hu, hv, ↓reduceIte]
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      · simp [F, hu, hv]
  have hFsize : ∀ s ∈ P, (F s).card ≤ 2 := by
    intro s hs
    by_cases hu : u ∈ s
    · simp only [F, hu, ↓reduceIte]
      have hh := Finset.card_filter_le (s.erase u) (fun x => x ∈ N)
      rw [Finset.card_erase_of_mem hu, (hcl s hs).card_eq] at hh
      omega
    · by_cases hv : v ∈ s
      · simp only [F, hu, hv, ↓reduceIte]
        have hh := Finset.card_filter_le (s.erase v) (fun x => x ∈ N)
        rw [Finset.card_erase_of_mem hv, (hcl s hs).card_eq] at hh
        omega
      · simp [F, hu, hv]
  have hBsize : ∀ e ∈ B, e.card ≤ 2 := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    exact hFsize s hs
  have hNsub : N ⊆ B.biUnion id := by
    intro w hw
    have hwN := (Finset.mem_filter.mp hw).2
    obtain ⟨s, hs, hws, hus | hvs⟩ :=
      simple_graph_common_neighbor_meets_packing_star G u v P huv hmax havoid w hwN.1 hwN.2
    · apply Finset.mem_biUnion.mpr
      refine ⟨F s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
      have hwu : w ≠ u := (G.ne_of_adj hwN.1).symm
      simp [F, hus, hws, hwu, hw]
    · apply Finset.mem_biUnion.mpr
      refine ⟨F s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
      have hwv : w ≠ v := (G.ne_of_adj hwN.2).symm
      have hunot : u ∉ s := by
        intro hu
        exact havoid s hs ⟨hu, hvs⟩
      simp [F, hunot, hvs, hws, hwv, hw]
  obtain ⟨M, hMB, hMdis, hMtwo, hbound⟩ := finset_rank_two_cover_matching_bound B hBsize
  refine ⟨M, hMdis, ?_, ?_⟩
  · intro e he
    have heB : e ∈ B := hMB he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp heB
    refine ⟨hMtwo _ he, ?_, ?_⟩
    · intro x hx
      have hxN := hFN s hx
      exact (Finset.mem_filter.mp hxN).2
    · intro x hx y hy hxy
      exact (hcl s hs).isClique (hFsub s hx) (hFsub s hy) hxy
  · have hNcard := Finset.card_le_card hNsub
    have hBcard : B.card ≤ P.card := Finset.card_image_le
    change N.card ≤ P.card + M.card
    omega
