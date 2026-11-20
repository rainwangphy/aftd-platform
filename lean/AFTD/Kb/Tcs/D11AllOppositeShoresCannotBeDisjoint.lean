import AFTD.Prelude
import AFTD.Kb.Tcs.D11SaturatedOppositeTargetImpossible
import AFTD.Kb.Tcs.D11AllOppositeShoresDisjointSaturates

/-!
# d11_all_opposite_shores_cannot_be_disjoint

Topic: graphs   Node: 7bac6c5ae4a2

Provenance: helper lemma. OP-1957 d=11 factor-critical bridge-family analysis; scratch Lean axiom audit completed.

A degree-saturated four-shore family cannot have all external opposite endpoints use disjoint shores.
-/

theorem d11_all_opposite_shores_cannot_be_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V) (z₀ : V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hB : B ⊆ S ∪ C) (hBcard : B.card=8) (hBS : (B ∩ S).card ≤ 2)
    (hE : 6 ≤ (B ∩ C).card) (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B)
    (hBA : ∀ e ∈ B ∩ C, ∀ a ∈ A, H.Adj e a)
    (hED : ∀ e ∈ B ∩ C, W e = S \ A) : False := by
  classical
  have hEsat := d11_all_opposite_shores_disjoint_saturates H S C A B Q W z₀
    hSC hS hA hAcard hE hz₀ hQ₀ hmax hQ hdis hsize havoid hzQ hcross hBA hED
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < (B ∩ C).card)
  have heC : e ∈ C := (Finset.mem_inter.mp he).2
  have hDsize : (S \ A).card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    omega
  have hQesize : (Q e).card=6 := by
    have hs := hsize e heC
    rw [hED e he,hDsize] at hs
    omega
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (by omega : 0 < (Q e).card)
  have htC : t ∈ C := by
    rcases Finset.mem_union.mp (hQ e heC ht) with htS | htC
    · by_cases htA : t ∈ A
      · exact ((Finset.disjoint_left.mp (havoid e heC)) htA ht).elim
      · have htD : t ∈ S \ A := Finset.mem_sdiff.mpr ⟨htS,htA⟩
        have htW : t ∈ W e := (hED e he).symm ▸ htD
        exact ((Finset.disjoint_left.mp (hdis e heC)) ht htW).elim
    · exact htC
  have htD : ∀ w ∈ S \ A, H.Adj t w := by
    intro w hw
    have hwW : w ∈ W e := (hED e he).symm ▸ hw
    exact hcross e heC t ht w hwW
  exact d11_saturated_opposite_target_impossible H S C A B Q W
    hSC hS hA hAcard hB hBcard hBS hE hmax hQ hW hdis hsize hQ4 havoid hzQ hcross hnest hEsat t htC htD
