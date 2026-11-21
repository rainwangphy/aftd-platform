import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyHasNoFullFirstNeighborhoodShore
import AFTD.Kb.Tcs.BridgeFamilyVariableExternalIncidenceBudget
import AFTD.Kb.Tcs.BridgeFamilyVariableRefinedWalkBudget
import AFTD.Kb.Tcs.BridgeFamilyVariableRefinedWalkBudgetStrict

/-!
# d11_eighteen_external_bridge_family_forces_four_shore

Topic: graphs   Node: 9100874a5d61

Provenance: helper lemma. OP-1957 d=11 bridge-family analysis; scratch Lean axiom audit completed.

The displayed bridge-family walk count forces a four-vertex shore when there are at least eighteen external vertices.
-/

theorem d11_eighteen_external_bridge_family_forces_four_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : 18 ≤ C.card) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card+1=11)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card + (W z).card = 12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card) (hWeven : ∀ z ∈ C, Even (W z).card) :
    ∃ z ∈ C, (W z).card=4 := by
  classical
  by_contra hnone
  have hsz : ∀ z ∈ C, (Q z).card + (W z).card = 11 + 1 := fun z hz => by
    have hsum0 := hsize z hz; omega
  have hfam : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=11+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := fun z hz =>
    ⟨Q z, W z, hdis z hz, hQ z hz, hW z hz, hsz z hz, hzQ z hz, hcross z hz⟩
  have hsix : ∀ z ∈ C, (W z).card = 6 ∨ (W z).card = 8 := by
    intro z hz
    have hne : (W z).card ≠ 4 := fun hcase0 => hnone ⟨z, hz, hcase0⟩
    have hneS := bridge_family_has_no_full_first_neighborhood_shore H S C 11 hSC hS hmax hfam
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (hsz z hz) (hzQ z hz) (hcross z hz)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hW z hz, hneS⟩)
    have hfour0 := hWmin z hz
    obtain ⟨mm0, hm⟩ := hWeven z hz
    omega
  have hprod : ∀ z ∈ C, 32 ≤ (W z).card * (Q z).card := by
    intro z hz
    have hsum0 := hsize z hz
    rcases hsix z hz with hcase0 | hcase0
    · have hqc0 : (Q z).card = 6 := by omega
      rw [hcase0, hqc0]; norm_num
    · have hqc0 : (Q z).card = 4 := by omega
      rw [hcase0, hqc0]
  by_cases hall : ∀ z ∈ C, (W z).card = 8
  · have hinc := bridge_family_variable_external_incidence_budget H S C 11 8 hSC hS hmax Q W
      hdis hQ hW hsz hzQ hcross (fun z hz => (hall z hz).ge)
    have hwalk := bridge_family_variable_refined_walk_budget H x y hxy S C 11 32 8 (by norm_num)
      (by omega) hSC hxC hyC hS hmax hSxy Q W hdis hQ hW hsz hxQ hyQ hzQ hcross
      (fun z hz => (hall z hz).ge) hprod
    dsimp only at hinc hwalk
    omega
  · push_neg at hall
    obtain ⟨z0, hz0, hne⟩ := hall
    have hsix0 : (W z0).card = 6 := by
      rcases hsix z0 hz0 with hcase0 | hcase0
      · exact hcase0
      · exact absurd hcase0 hne
    have hq6 : (Q z0).card = 6 := by have hsum0 := hsize z0 hz0; omega
    have hW6 : ∀ z ∈ C, 6 ≤ (W z).card := fun z hz => by
      rcases hsix z hz with hcase0 | hcase0 <;> omega
    have hinc := bridge_family_variable_external_incidence_budget H S C 11 6 hSC hS hmax Q W
      hdis hQ hW hsz hzQ hcross hW6
    have hwalk := bridge_family_variable_refined_walk_budget_strict H x y hxy S C 11 32 6
      (by norm_num) (by omega) hSC hxC hyC hS hmax hSxy Q W hdis hQ hW hsz hxQ hyQ hzQ hcross
      hW6 hprod ⟨z0, hz0, by rw [hsix0, hq6]; norm_num⟩
    dsimp only at hinc hwalk
    omega
