import AFTD.Prelude

/-!
# d11_all_opposite_shores_disjoint_saturates

Topic: graphs   Node: 2e2922b32b23

Provenance: helper lemma. OP-1957 d=11 factor-critical bridge-family analysis; scratch Lean axiom audit completed.

A degree-saturated four-shore family obeys the displayed opposite-target neighborhood restriction.
-/

theorem d11_all_opposite_shores_disjoint_saturates
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V) (z₀ : V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hE : 6 ≤ (B ∩ C).card) (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hBA : ∀ e ∈ B ∩ C, ∀ a ∈ A, H.Adj e a)
    (hED : ∀ e ∈ B ∩ C, W e = S \ A) :
    ∀ e ∈ B ∩ C, ∀ w ∈ S \ A, ¬ H.Adj e w := by
  classical
  let D := S \ A
  have hDsize : D.card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    dsimp [D]
    omega
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_sdiff.mp ha).1 hc
  have hEsub : B ∩ C ⊆ H.neighborFinset z₀ := by
    intro e he
    have heQ : e ∈ Q z₀ := hQ₀.symm ▸ (Finset.mem_inter.mp he).1
    exact (H.mem_neighborFinset z₀ e).mpr (hzQ z₀ hz₀ e heQ)
  intro e he w hw hew
  have heC : e ∈ C := (Finset.mem_inter.mp he).2
  have heB : e ∈ B := (Finset.mem_inter.mp he).1
  have heQ0 : e ∈ Q z₀ := hQ₀.symm ▸ heB
  have hrootedge : H.Adj e z₀ := (hzQ z₀ hz₀ e heQ0).symm
  have hQeC : Q e ⊆ C := by
    intro q hq
    rcases Finset.mem_union.mp (hQ e heC hq) with hqS | hqC
    · by_cases hqA : q ∈ A
      · exact ((Finset.disjoint_left.mp (havoid e heC)) hqA hq).elim
      · have hqD : q ∈ D := Finset.mem_sdiff.mpr ⟨hqS,hqA⟩
        have hqW : q ∈ W e := (hED e he).symm ▸ hqD
        exact ((Finset.disjoint_left.mp (hdis e heC)) hq hqW).elim
    · exact hqC
  have hQesize : (Q e).card=6 := by
    have hs := hsize e heC
    rw [hED e he] at hs
    change (Q e).card + D.card = 12 at hs
    omega
  have hrootnotQ : z₀ ∉ Q e := by
    intro hzQe
    have hDsub : D ⊆ H.neighborFinset z₀ := by
      intro a ha
      have haW : a ∈ W e := (hED e he).symm ▸ ha
      exact (H.mem_neighborFinset z₀ a).mpr (hcross e heC z₀ hzQe a haW)
    have hd : Disjoint D (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hDC) ha (Finset.mem_inter.mp hb).2
    have hc := Finset.card_le_card (Finset.union_subset hDsub hEsub)
    rw [Finset.card_union_of_disjoint hd,hDsize] at hc
    have hm := hmax z₀
    omega
  have hAQ : Disjoint A (Q e) := havoid e heC
  have hrootA : z₀ ∉ A := fun h => (Finset.disjoint_left.mp hSC) (hA h) hz₀
  have hrootnot : z₀ ∉ A ∪ Q e := by simp [hrootA,hrootnotQ]
  have hwA : w ∉ A := (Finset.mem_sdiff.mp hw).2
  have hwC : w ∉ C := fun h => (Finset.disjoint_left.mp hSC) (Finset.mem_sdiff.mp hw).1 h
  have hwQ : w ∉ Q e := fun h => hwC (hQeC h)
  have hwroot : w ≠ z₀ := fun h => hwC (h ▸ hz₀)
  have hwnot : w ∉ insert z₀ (A ∪ Q e) := by simp [hwroot,hwA,hwQ]
  have hsub : insert w (insert z₀ (A ∪ Q e)) ⊆ H.neighborFinset e := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_union] at ha
    rcases ha with rfl | rfl | ha | ha
    · simpa using hew
    · simpa using hrootedge
    · simpa using hBA e he a ha
    · simpa using hzQ e heC a ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hwnot,Finset.card_insert_of_notMem hrootnot,
    Finset.card_union_of_disjoint hAQ,hAcard,hQesize] at hc
  have hm := hmax e
  omega
