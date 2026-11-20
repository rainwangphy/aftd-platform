import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyEvenOppositeShoreAtLeastFour
import AFTD.Kb.Tcs.BridgeFamilyVariableShoreIncidenceWalkBudget
import AFTD.Kb.Tcs.FourVertexShoresForceManyComplementWalks

/-!
# d11_large_bridge_family_forces_four_shore

Topic: graphs   Node: 4b4b056f8a8b

Provenance: helper lemma. OP-1957 variable-shore incidence and padded-walk bound.

A d=11 bridge-shore family with at least twenty external vertices must contain a four-vertex shore.
-/

theorem d11_large_bridge_family_forces_four_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : 20 ≤ C.card) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card+1=11)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card + (W z).card = 12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card)
    (hQeven : ∀ z ∈ C, Even (Q z).card) (hWeven : ∀ z ∈ C, Even (W z).card) :
    ∃ z ∈ C, (W z).card = 4 := by
  classical
  by_contra hnone
  have hW6 : ∀ z ∈ C, 6 ≤ (W z).card := by
    intro z hz
    have hne : (W z).card ≠ 4 := fun h => hnone ⟨z,hz,h⟩
    have h4 := hWmin z hz
    obtain ⟨m,hm⟩ := hWeven z hz
    omega
  have hfam : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=11+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := by
    intro z hz
    exact ⟨Q z,W z,hdis z hz,hQ z hz,hW z hz,by simpa using hsize z hz,hzQ z hz,hcross z hz⟩
  have hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card := by
    intro z hz
    have hq4 := bridge_family_even_opposite_shore_at_least_four H S C 11 hSC hS hmax hfam
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (by simpa using hsize z hz)
      (hzQ z hz) (hcross z hz) (hQeven z hz)
    have hp := four_vertex_shores_force_many_complement_walks 11 (W z).card (Q z).card
      (hWmin z hz) hq4 (by have hs := hsize z hz; omega)
    norm_num at hp
    exact hp
  have hb := bridge_family_variable_shore_incidence_walk_budget H x y hxy S C 11 32 6
    (by omega) (by omega) hSC hxC hyC hS hmax hSxy Q W hdis hQ hW
    (by intro z hz; simpa using hsize z hz) hxQ hyQ hzQ hcross hW6 hprod
  obtain ⟨hinc,hwalk⟩ := hb
  norm_num at hinc hwalk
  omega
