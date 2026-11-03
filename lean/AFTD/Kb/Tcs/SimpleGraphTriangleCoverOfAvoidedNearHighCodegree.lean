import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCommonNeighborsMatchingOfAvoidedPacking
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverOfNearFullCommonMatching
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber

/-!
# simple_graph_triangle_cover_of_avoided_near_high_codegree

Topic: graphs   Node: 0151f165cf35

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign, related to matching-cover reductions in https://arxiv.org/abs/2610.15269; see state/campaigns/triangle_reductions/high_codegree_route_in512.md.

If a maximum triangle packing avoids an edge with at least twice the packing number minus one common neighbors and the packing number is at least two, the triangle cover number is at most twice the packing number.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_cover_of_avoided_near_high_codegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (P : Finset (Finset V)) (huv : G.Adj u v)
    (hcl : ∀ t ∈ P, G.IsNClique 3 t)
    (hmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card)
    (havoid : ∀ s ∈ P, ¬(u ∈ s ∧ v ∈ s))
    (hsize : P.card = simple_graph_triangle_packing_number G)
    (hPtwo : 2 ≤ P.card)
    (hlarge : 2 * P.card ≤
      ((Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)).card + 1) :
    simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  classical
  let N : Finset V := (Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)
  obtain ⟨M, hMdis, hMprop, hMbound⟩ :=
    simple_graph_common_neighbors_matching_of_avoided_packing G u v P huv hcl hmax havoid
  have hsubcard : P.card - 1 ≤ M.card := by omega
  obtain ⟨M0, hM0sub, hM0card⟩ := Finset.exists_subset_card_eq hsubcard
  have hM0dis : (M0 : Set (Finset V)).Pairwise Disjoint := by
    intro e he f hf hef
    exact hMdis (hM0sub he) (hM0sub hf) hef
  have hUcard : (M0.biUnion id).card ≤ 2 * M0.card := by
    calc
      (M0.biUnion id).card ≤ ∑ e ∈ M0, e.card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ M0, 2 := by
        apply Finset.sum_le_sum
        intro e he
        exact le_of_eq (hMprop e (hM0sub he)).1
      _ = 2 * M0.card := by simp [Nat.mul_comm]
  have hnot : ¬N ⊆ M0.biUnion id := by
    intro hs
    have hh := Finset.card_le_card hs
    change 2 * P.card ≤ N.card + 1 at hlarge
    rw [hM0card] at hUcard
    omega
  obtain ⟨w, hwN, hwU⟩ := Finset.not_subset.mp hnot
  have hw' : G.Adj u w ∧ G.Adj v w := (Finset.mem_filter.mp hwN).2
  have hM0prop : ∀ e ∈ M0, e.card = 2 ∧ w ∉ e ∧
      (∀ x ∈ e, G.Adj u x ∧ G.Adj v x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y) := by
    intro e he
    have hp := hMprop e (hM0sub he)
    refine ⟨hp.1, ?_, hp.2⟩
    intro hw
    apply hwU
    exact Finset.mem_biUnion.mpr ⟨e, he, hw⟩
  have hnum : simple_graph_triangle_packing_number G = M0.card + 1 := by
    rw [hM0card, ← hsize]
    omega
  have hc := simple_graph_triangle_cover_of_near_full_common_matching G u v w M0
    huv hw'.1 hw'.2 hM0prop hM0dis hnum
  rw [hM0card] at hc
  omega
