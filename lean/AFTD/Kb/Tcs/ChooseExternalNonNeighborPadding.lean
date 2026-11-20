import AFTD.Prelude
import AFTD.Kb.Tcs.ExternalNeighborCountWithRInternal

/-!
# choose_external_non_neighbor_padding

Topic: graphs   Node: 81965f58f4b1

Provenance: helper lemma. OP-1957 variable-shore bridge-family incidence and padded-walk count.

The external set supplies r−3 nonneighbors for a padded-walk construction.
-/

theorem choose_external_non_neighbor_padding {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (q : V) (S C : Finset V) (d r : ℕ)
    (hSC : Disjoint S C) (hr : 4 ≤ r) (hCr : d ≤ C.card)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hqin : r ≤ ((H.neighborFinset q) ∩ S).card) :
    ∃ P : Finset V, P ⊆ C \ H.neighborFinset q ∧ P.card = r-3 := by
  classical
  have hnc := external_neighbor_count_with_r_internal H q S C d r hSC hmax hqin
  let N := (H.neighborFinset q) ∩ C
  have hNsub : N ⊆ C := Finset.inter_subset_right
  have hc := Finset.card_sdiff_add_card_eq_card hNsub
  have hbound : r-3 ≤ (C \ N).card := by
    dsimp [N] at hc ⊢
    omega
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hbound
  refine ⟨P,?_,hcard⟩
  intro a ha
  have ha' := hP ha
  simp only [N,Finset.mem_sdiff,Finset.mem_inter,not_and] at ha' ⊢
  exact ⟨ha'.1, fun h => ha'.2 h ha'.1⟩
