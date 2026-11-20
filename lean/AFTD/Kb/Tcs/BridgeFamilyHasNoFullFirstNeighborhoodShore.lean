import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeOppositeShoreHasTwoExternalVertices

/-!
# bridge_family_has_no_full_first_neighborhood_shore

Topic: graphs   Node: d46155184358

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family; no first zero-codegree witness required.

A family of bridge witnesses at every external vertex cannot have a shore equal to the whole first neighborhood.
-/

theorem bridge_family_has_no_full_first_neighborhood_shore {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S C : Finset V) (d : ℕ)
    (hSC : Disjoint S C) (hS : S.card+1=d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hfamily : ∀ z ∈ C, ∃ Q W : Finset V, Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧
      Q.card+W.card=d+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w)) :
    ∀ z ∈ C, ∀ Q W : Finset V, Disjoint Q W → Q ⊆ S ∪ C → W ⊆ S →
      Q.card+W.card=d+1 → (∀ q ∈ Q, H.Adj z q) →
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) → W ≠ S := by
  classical
  intro z hz Q W hQW hQ hW hsize hzQ hcross heq
  have htwo := bridge_opposite_shore_has_two_external_vertices S C Q W d hSC hQW hQ hW hS hsize
  have hne : (Q ∩ C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := hne
  have hqQ : q ∈ Q := (Finset.mem_inter.mp hq).1
  have hqC : q ∈ C := (Finset.mem_inter.mp hq).2
  obtain ⟨Q',W',hQW',hQ',hW',hsize',hqQ',hcross'⟩ := hfamily q hqC
  have htwo' := bridge_opposite_shore_has_two_external_vertices S C Q' W' d hSC hQW' hQ' hW' hS hsize'
  have hdis : Disjoint S (Q' ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) ha (Finset.mem_inter.mp hb).2
  have hsub : S ∪ (Q' ∩ C) ⊆ H.neighborFinset q := by
    intro a ha
    rw [H.mem_neighborFinset]
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hcross q hqQ a (heq.symm ▸ ha)
    · exact hqQ' a (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hm := hmax q
  omega
