import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyHasNoFullFirstNeighborhoodShore

/-!
# bridge_family_even_opposite_shore_at_least_four

Topic: graphs   Node: 3f9d86bd1eb3

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family; no first zero-codegree witness required.

Every even opposite shore in such a bridge family has at least four vertices.
-/

theorem bridge_family_even_opposite_shore_at_least_four {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S C : Finset V) (d : ℕ)
    (hSC : Disjoint S C) (hS : S.card+1=d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hfamily : ∀ z ∈ C, ∃ Q W : Finset V, Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧
      Q.card+W.card=d+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w)) :
    ∀ z ∈ C, ∀ Q W : Finset V, Disjoint Q W → Q ⊆ S ∪ C → W ⊆ S →
      Q.card+W.card=d+1 → (∀ q ∈ Q, H.Adj z q) →
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) → Even Q.card → 4 ≤ Q.card := by
  classical
  intro z hz Q W hQW hQ hW hsize hzQ hcross hqe
  have hne := bridge_family_has_no_full_first_neighborhood_shore H S C d hSC hS hmax hfamily
    z hz Q W hQW hQ hW hsize hzQ hcross
  have hss : W ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hW,hne⟩
  have hlt := Finset.card_lt_card hss
  obtain ⟨m,hm⟩ := hqe
  omega
