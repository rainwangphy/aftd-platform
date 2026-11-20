import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeOppositeShoreHasTwoExternalVertices
import AFTD.Kb.Tcs.ExternalNeighborCountWithFourInternal

/-!
# bridge_family_external_incidence_budget

Topic: graphs   Node: 7ac8ef5a89da

Provenance: helper lemma. OP-1957 refined saturated-twin bridge-family incidence and walk count.

At least two opposite-shore incidences per endpoint are supported by external vertices with at least four internal neighbors.
-/

theorem bridge_family_external_incidence_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card) :
    let T := C.filter (fun q => 4 ≤ ((H.neighborFinset q) ∩ S).card)
    2*C.card ≤ (d-4)*T.card := by
  classical
  let T := C.filter (fun q => 4 ≤ ((H.neighborFinset q) ∩ S).card)
  let lower : Finset (V × V) := C.biUnion fun z => (Q z ∩ C).image (fun q => (z,q))
  have hitem : ∀ z, ((Q z ∩ C).image (fun q => (z,q))).card = (Q z ∩ C).card := by
    intro z
    exact Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.snd h)
  have hpair : (C : Set V).PairwiseDisjoint (fun z => (Q z ∩ C).image (fun q => (z,q))) := by
    intro z hz z' hz' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp ht
    obtain ⟨q',hq',he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg Prod.fst he).trans (congrArg Prod.fst he').symm
  have hlo : 2*C.card ≤ lower.card := by
    dsimp [lower]
    rw [Finset.card_biUnion hpair]
    have hs : ∑ z ∈ C, 2 ≤ ∑ z ∈ C, (Q z ∩ C).card := by
      apply Finset.sum_le_sum
      intro z hz
      exact bridge_opposite_shore_has_two_external_vertices S C (Q z) (W z) d hSC
        (hdis z hz) (hQ z hz) (hW z hz) hSsize (hsize z hz)
    simp only [hitem] at *
    simpa [Nat.mul_comm] using hs
  let upper : Finset (V × V) := T.biUnion fun q =>
    ((H.neighborFinset q) ∩ C).image (fun z => (z,q))
  have hup : upper.card ≤ T.card*(d-4) := by
    dsimp [upper]
    apply Finset.card_biUnion_le_card_mul
    intro q hq
    have hq4 : 4 ≤ ((H.neighborFinset q) ∩ S).card := (Finset.mem_filter.mp hq).2
    have hc := external_neighbor_count_with_four_internal H q S C d hSC (hmax q) hq4
    calc
      (((H.neighborFinset q) ∩ C).image (fun z => (z,q))).card ≤ ((H.neighborFinset q) ∩ C).card := Finset.card_image_le
      _ ≤ d-4 := by omega
  have hsub : lower ⊆ upper := by
    intro t ht
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    have hqQ : q ∈ Q z := (Finset.mem_inter.mp hq).1
    have hqC : q ∈ C := (Finset.mem_inter.mp hq).2
    have hq4 : 4 ≤ ((H.neighborFinset q) ∩ S).card := by
      have hsub : W z ⊆ (H.neighborFinset q) ∩ S := by
        intro w hw
        exact Finset.mem_inter.mpr ⟨by simpa using hcross z hz q hqQ w hw,hW z hz hw⟩
      have hc := Finset.card_le_card hsub
      have hm := hWmin z hz
      omega
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hqC,hq4⟩
    have hzN : z ∈ H.neighborFinset q := by simpa using (hzQ z hz q hqQ).symm
    apply Finset.mem_biUnion.mpr
    refine ⟨q,hqT,Finset.mem_image.mpr ⟨z,Finset.mem_inter.mpr ⟨hzN,hz⟩,rfl⟩⟩
  have hb := le_trans hlo (le_trans (Finset.card_le_card hsub) hup)
  simpa [Nat.mul_comm] using hb
