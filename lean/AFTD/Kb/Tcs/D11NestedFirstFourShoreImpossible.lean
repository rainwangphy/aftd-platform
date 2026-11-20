import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourShoresExternalOppositeImpossible
import AFTD.Kb.Tcs.D11DisjointOppositeShoreHasNoOppositeNeighbors
import AFTD.Kb.Tcs.D11EightShoreCannotTargetNestedOpposite
import AFTD.Kb.Tcs.D11SixShoreCannotTargetNestedSix
import AFTD.Kb.Tcs.D11AllOppositeShoresCannotBeDisjoint

/-!
# d11_nested_first_four_shore_impossible

Topic: graphs   Node: 496f7e1d9792

Provenance: helper lemma. OP-1957 d=11 saturated-twin family; scratch Lean axiom audit completed.

The displayed factor-critical crossing bridge family has no four-vertex shore.
-/

theorem d11_nested_first_four_shore_impossible
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y z₀ : V) (hxy : x ≠ y) (S C A B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hB : B ⊆ S ∪ C) (hBcard : B.card=8) (hBS : (B ∩ S).card ≤ 2)
    (hE : 6 ≤ (B ∩ C).card) (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (hW₀ : W z₀ = A)
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card) (hW4 : ∀ z ∈ C, 4 ≤ (W z).card)
    (hWeven : ∀ z ∈ C, Even (W z).card)
    (hW8 : ∀ z ∈ B ∩ C, (W z).card ≤ 8)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B) : False := by
  classical
  have hBAall : ∀ e ∈ B, ∀ a ∈ A, H.Adj e a := by
    intro e he a ha
    have heQ : e ∈ Q z₀ := hQ₀.symm ▸ he
    have haW : a ∈ W z₀ := hW₀.symm ▸ ha
    exact hcross z₀ hz₀ e heQ a haW
  have hBA : ∀ e ∈ B ∩ C, ∀ a ∈ A, H.Adj e a := by
    intro e he a ha
    exact hBAall e (Finset.mem_inter.mp he).1 a ha
  have hDsize : (S \ A).card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    omega
  have hno4 : ∀ e ∈ B ∩ C, (W e).card ≠ 4 := by
    intro e he hw4
    have heC : e ∈ C := (Finset.mem_inter.mp he).2
    have hQ8 : (Q e).card=8 := by have hs := hsize e heC; omega
    exact two_four_shores_external_opposite_impossible H x y e hxy S A B (Q e) (W e)
      hA (hW e heC) hAcard hBcard hQ8 hw4 hBS hxB hyB (Finset.mem_inter.mp he).1
      hmax hSxy hBAall (hzQ e heC) (hcross e heC)
  have hclass : ∀ e ∈ B ∩ C, W e = S \ A ∨ (A ⊆ W e ∧ Q e ⊆ B) := by
    intro e he
    have heC : e ∈ C := (Finset.mem_inter.mp he).2
    by_cases hne : (A ∩ W e).Nonempty
    · exact Or.inr (hnest e heC hne)
    · left
      have hwD : W e ⊆ S \ A := by
        intro w hw
        refine Finset.mem_sdiff.mpr ⟨hW e heC hw,?_⟩
        intro hwA
        exact hne ⟨w,Finset.mem_inter.mpr ⟨hwA,hw⟩⟩
      have hwle := Finset.card_le_card hwD
      have hw4 := hW4 e heC
      have hwne := hno4 e he
      obtain ⟨m,hm⟩ := hWeven e heC
      have hwsize : (W e).card=6 := by omega
      exact Finset.eq_of_subset_of_card_le hwD (by omega)
  have htarget : ∀ e ∈ B ∩ C, Q e ⊆ B → ∃ q ∈ Q e ∩ (B ∩ C), True := by
    intro e he hQB
    have heC : e ∈ C := (Finset.mem_inter.mp he).2
    by_contra hn
    have hnC : ∀ q ∈ Q e, q ∉ C := by
      intro q hq hqc
      apply hn
      exact ⟨q,Finset.mem_inter.mpr ⟨hq,Finset.mem_inter.mpr ⟨hQB hq,hqc⟩⟩,trivial⟩
    have hs : Q e ⊆ B ∩ S := by
      intro q hq
      refine Finset.mem_inter.mpr ⟨hQB hq,?_⟩
      rcases Finset.mem_union.mp (hQ e heC hq) with hqS | hqC
      · exact hqS
      · exact ((hnC q hq) hqC).elim
    have hc := Finset.card_le_card hs
    have hq4 := hQ4 e heC
    omega
  have htargetnested : ∀ e ∈ B ∩ C, Q e ⊆ B →
      ∃ q ∈ Q e ∩ (B ∩ C), A ⊆ W q ∧ Q q ⊆ B := by
    intro e he hQB
    obtain ⟨q,hq,_⟩ := htarget e he hQB
    have hqQ : q ∈ Q e := (Finset.mem_inter.mp hq).1
    have hqE : q ∈ B ∩ C := (Finset.mem_inter.mp hq).2
    rcases hclass q hqE with hd | hn
    · have hno := d11_disjoint_opposite_shore_has_no_opposite_neighbors H S C A B Q W z₀ q
        hSC hS hA hAcard hE hz₀ hQ₀ hqE hmax hQ hdis hsize havoid hzQ hcross hBA hd
      have heC : e ∈ C := (Finset.mem_inter.mp he).2
      exact (hno e he (hzQ e heC q hqQ).symm).elim
    · exact ⟨q,hq,hn⟩
  have hno8 : ∀ e ∈ B ∩ C, A ⊆ W e → Q e ⊆ B → (W e).card ≠ 8 := by
    intro e he hAW hQB hw8
    obtain ⟨q,hq,hAq,hQq⟩ := htargetnested e he hQB
    exact d11_eight_shore_cannot_target_nested_opposite H x y z₀ e q hxy S C B Q W
      hSC hxC hyC hB hBS hz₀ hQ₀ (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hq).2
      (Finset.mem_inter.mp hq).1 hw8 hQq hmax hSxy hW hsize hQ4 hzQ hcross
  have hED : ∀ e ∈ B ∩ C, W e = S \ A := by
    intro e he
    rcases hclass e he with hd | ⟨hAW,hQB⟩
    · exact hd
    · have heC : e ∈ C := (Finset.mem_inter.mp he).2
      have hw4 := hW4 e heC
      have hwne4 := hno4 e he
      have hwle := hW8 e he
      have hwne8 := hno8 e he hAW hQB
      obtain ⟨m,hm⟩ := hWeven e heC
      have hw6 : (W e).card=6 := by omega
      obtain ⟨q,hq,hAq,hQq⟩ := htargetnested e he hQB
      have hqE := (Finset.mem_inter.mp hq).2
      have hqC := (Finset.mem_inter.mp hqE).2
      have hqw4 := hW4 q hqC
      have hqwne4 := hno4 q hqE
      have hqwle := hW8 q hqE
      have hqwne8 := hno8 q hqE hAq hQq
      obtain ⟨n,hn⟩ := hWeven q hqC
      have hqw6 : (W q).card=6 := by omega
      exact (d11_six_shore_cannot_target_nested_six H z₀ e q S C B Q W
        hSC hB hBcard hBS hz₀ hQ₀ he hqE (Finset.mem_inter.mp hq).1 hw6 hqw6
        hQB hQq hmax hW hdis hsize hzQ hcross).elim
  exact d11_all_opposite_shores_cannot_be_disjoint H S C A B Q W z₀
    hSC hS hA hAcard hB hBcard hBS hE hz₀ hQ₀ hmax hQ hW hdis hsize hQ4 havoid hzQ hcross hnest hBA hED
