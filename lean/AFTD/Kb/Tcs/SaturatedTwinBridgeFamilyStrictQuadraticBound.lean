import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyEvenOppositeShoreAtLeastFour
import AFTD.Kb.Tcs.BridgeFamilyStrictWalkBudget
import AFTD.Kb.Tcs.FourVertexShoresForceManyComplementWalks
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# saturated_twin_bridge_family_strict_quadratic_bound

Topic: graphs   Node: 5255ce4e25c0

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family, without the first zero-codegree witness.

A nonempty even bridge-shore family satisfies 4|C|<(d−1)(d−2).
-/

theorem saturated_twin_bridge_family_strict_quadratic_bound
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hC : C.Nonempty) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card+1=d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card + (W z).card = d+1)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 2 ≤ (W z).card)
    (hQeven : ∀ z ∈ C, Even (Q z).card) (hWeven : ∀ z ∈ C, Even (W z).card) :
    4*C.card < (d-1)*(d-2) := by
  classical
  have hfam : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=d+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := by
    intro z hz
    exact ⟨Q z,W z,hdis z hz,hQ z hz,hW z hz,hsize z hz,hzQ z hz,hcross z hz⟩
  have hq4 : ∀ z ∈ C, 4 ≤ (Q z).card := by
    intro z hz
    exact bridge_family_even_opposite_shore_at_least_four H S C d hSC hS hmax hfam
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (hsize z hz)
      (hzQ z hz) (hcross z hz) (hQeven z hz)
  have hw4 : ∀ z ∈ C, 4 ≤ (W z).card := by
    intro z hz
    have hWne : (W z).Nonempty := Finset.card_pos.mp (by have := hWmin z hz; omega)
    obtain ⟨w,hw⟩ := hWne
    have hx : H.Adj w x := (hSxy w (hW z hz hw)).1
    have hy : H.Adj w y := (hSxy w (hW z hz hw)).2
    have hsub : insert x (insert y (Q z)) ⊆ H.neighborFinset w := by
      intro a ha
      rw [H.mem_neighborFinset]
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact hx
      · exact hy
      · exact (hcross z hz a ha w hw).symm
    have hxnot : x ∉ insert y (Q z) := by simp [hxy,hxQ z hz]
    have hyNot : y ∉ Q z := hyQ z hz
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxnot, Finset.card_insert_of_notMem hyNot] at hc
    have hm := hmax w
    obtain ⟨m,hm'⟩ := hWeven z hz
    have hs := hsize z hz
    omega
  have hprod : ∀ z ∈ C, 4*(d-3) ≤ (W z).card*(Q z).card := by
    intro z hz
    exact four_vertex_shores_force_many_complement_walks d (W z).card (Q z).card
      (hw4 z hz) (hq4 z hz) (by have hs := hsize z hz; omega)
  have hb := bridge_family_strict_walk_budget H x y hxy S C d (4*(d-3)) hC hSC hxC hyC hS hmax hSxy Q W hdis hQ hW hsize hxQ hyQ hzQ hcross hw4 hprod
  obtain ⟨z,hz⟩ := hC
  have hd3 : 3 < d := by
    have hs := hsize z hz
    have hq := hq4 z hz
    have hw := hw4 z hz
    omega
  have hp : 0 < d-3 := Nat.sub_pos_of_lt hd3
  have hmul : (4*C.card)*(d-3) < ((d-1)*(d-2))*(d-3) := by nlinarith [hb]
  exact (Nat.mul_lt_mul_right hp).mp hmul
