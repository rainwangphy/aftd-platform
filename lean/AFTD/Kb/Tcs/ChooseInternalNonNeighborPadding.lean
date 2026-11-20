import AFTD.Prelude
import AFTD.Kb.Tcs.InternalNeighborDegreeBudget

/-!
# choose_internal_non_neighbor_padding

Topic: graphs   Node: 26968dbd4425

Provenance: helper lemma. OP-1957 saturated-twin bridge-family walk count; scratch Lean axiom audit completed.

An internal vertex has enough external nonneighbors to pad its walk fiber by its internal degree minus one.
-/

theorem choose_internal_non_neighbor_padding
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hq : q ∈ S) (hCsize : d ≤ C.card)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hmax : (H.neighborFinset q).card ≤ d) :
    ∃ P : Finset V, P ⊆ C \ H.neighborFinset q ∧
      P.card = ((H.neighborFinset q) ∩ S).card-1 := by
  classical
  have hbudget := internal_neighbor_degree_budget H x y q hxy S C d hSC hxC hyC hq hSxy hmax
  let N := (H.neighborFinset q) ∩ C
  have hNsub : N ⊆ C := Finset.inter_subset_right
  have hc := Finset.card_sdiff_add_card_eq_card hNsub
  have hbound : ((H.neighborFinset q) ∩ S).card-1 ≤ (C \ N).card := by
    dsimp [N] at hc ⊢
    omega
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hbound
  refine ⟨P,?_,hcard⟩
  intro a ha
  have ha' := hP ha
  simp only [N,Finset.mem_sdiff,Finset.mem_inter,not_and] at ha' ⊢
  exact ⟨ha'.1, fun h => ha'.2 h ha'.1⟩
