import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeOppositeShoreHasTwoExternalVertices

/-!
# bridge_family_has_incomparable_shores

Topic: graphs   Node: c868afdebcac

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family; no first zero-codegree witness required.

Such a bridge family contains two incomparable shores, at endpoints linked by an opposite-shore incidence.
-/

theorem bridge_family_has_incomparable_shores {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S C : Finset V) (d : ℕ)
    (Q W : V → Finset V) (hC : C.Nonempty) (hSC : Disjoint S C) (hS : S.card+1=d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card + (W z).card = d+1)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w) :
    ∃ z ∈ C, ∃ q ∈ C, q ∈ Q z ∧ ¬ W q ⊆ W z ∧ ¬ W z ⊆ W q := by
  classical
  obtain ⟨z,hz,hmaxW⟩ := Finset.exists_max_image C (fun a => (W a).card) hC
  have htwo := bridge_opposite_shore_has_two_external_vertices S C (Q z) (W z) d hSC
    (hdis z hz) (hQ z hz) (hW z hz) hS (hsize z hz)
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (by omega : 0 < (Q z ∩ C).card)
  have hqQ : q ∈ Q z := (Finset.mem_inter.mp hq).1
  have hqC : q ∈ C := (Finset.mem_inter.mp hq).2
  have hnot : ¬ W q ⊆ W z := by
    intro hsub
    have hN : Q q ∪ W q ⊆ H.neighborFinset q := by
      intro a ha
      rw [H.mem_neighborFinset]
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hzQ q hqC a ha
      · exact hcross z hz q hqQ a (hsub ha)
    have hc := Finset.card_le_card hN
    rw [Finset.card_union_of_disjoint (hdis q hqC), hsize q hqC] at hc
    have hm := hmax q
    omega
  have hnot' : ¬ W z ⊆ W q := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hcm := hmaxW q hqC
    have heq : W z = W q := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hnot (heq ▸ Finset.Subset.refl _)
  exact ⟨z,hz,q,hqC,hqQ,hnot,hnot'⟩
