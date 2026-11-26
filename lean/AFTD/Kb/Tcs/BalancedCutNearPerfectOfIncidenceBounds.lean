import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# balanced_cut_near_perfect_of_incidence_bounds

Topic: graphs   Node: 9343eef8af14

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

Under the displayed incidence bounds, minimum degree and unmatched independence cardinality, a balanced-side matching has at least k−1 edges.
-/

theorem balanced_cut_near_perfect_of_incidence_bounds
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph) [DecidablePred (· ∈ M.verts)] (hM : M.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hindU : (C \ M.verts.toFinset).card ≤ k)
    (hbound : ∀ r : ℕ, 2 ≤ r → M.edgeSet.ncard + r = k →
      (∑ u ∈ C \ M.verts.toFinset, ((G.neighborFinset u) ∩ C).card) ≤ 2*r*(k-2*r+1) ∧
      (∑ u ∈ C \ M.verts.toFinset, ((G.neighborFinset u) ∩ Cᶜ).card) ≤ 2*r*k+2*r) :
    k ≤ M.edgeSet.ncard + 1 := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset (Fin (4*k)) := M.verts.toFinset
    let U : Finset (Fin (4*k)) := C \ D
    have hD : D.card = 2*M.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hM).symm
    have hDC : D ⊆ C := by
      intro v hv
      exact hMC (by simpa [D] using hv)
    have hmle : M.edgeSet.ncard ≤ k := by
      have hh := Finset.card_le_card hDC
      omega
    by_contra hnot
    let r := k-M.edgeSet.ncard
    have hr : 2 ≤ r := by dsimp [r]; omega
    have hm : M.edgeSet.ncard+r=k := by dsimp [r]; omega
    have hUcard : U.card = 2*r := by
      have hh := Finset.card_sdiff_add_card_eq_card hDC
      dsimp [U]
      omega
    have hstar := (hbound r hr hm).1
    have hcross := (hbound r hr hm).2
    change (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) ≤ 2*r*(k-2*r+1) at hstar
    change (∑ u ∈ U, ((G.neighborFinset u) ∩ Cᶜ).card) ≤ 2*r*k+2*r at hcross
    have hsplit : ∀ u,
        ((G.neighborFinset u) ∩ C).card + ((G.neighborFinset u) ∩ Cᶜ).card =
          (G.neighborFinset u).card := by
      intro u
      have hh := Finset.card_filter_add_card_filter_not (s:=G.neighborFinset u) (fun v => v ∈ C)
      simpa [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, Finset.sdiff_eq_inter_compl] using hh
    have hsum : (∑ u ∈ U, (G.neighborFinset u).card) =
        (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) +
        (∑ u ∈ U, ((G.neighborFinset u) ∩ Cᶜ).card) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      exact (hsplit u).symm
    have hdegreeSum : U.card*(2*k+1) ≤ ∑ u ∈ U, (G.neighborFinset u).card := by
      have hh := Finset.sum_le_sum (s:=U) (fun u _ => hdegree u)
      simpa using hh
    rw [hsum,hUcard] at hdegreeSum
    have hrk : 2*r ≤ k := by
      change U.card ≤ k at hindU
      omega
    have hsub : k-2*r+1+2*r=k+1 := by omega
    nlinarith
