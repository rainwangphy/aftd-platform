import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.ComplementAdjacentTwinsHaveEqualOpenNeighbors
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.FactorcriticalFalseTwinForcedBridgeResidualShores
import AFTD.Kb.Tcs.FactorcriticalInduceOneAfterVertexRestriction
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.Tcs.CrossingShoresForceTwoCommonOppositeVertices
import AFTD.Kb.Tcs.CrossingBridgeShoresForceCutEquality
import AFTD.Kb.Tcs.D11LargeBridgeFamilyForcesFourShore
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.G

/-!
# factorcritical_minimal_d11_kge9_excludes_saturated_twins

Topic: graphs   Node: e1cd95c43927

Provenance: original. Related work: https://arxiv.org/abs/2611.22690; the saturated complement-twin branch of OP-1957.

For k at least nine, a minimally k-extendible 2k-factor-critical graph of order 2k+14 whose complement has maximum degree at most eleven cannot have adjacent complement twins one of which has complement degree eleven.
-/

open SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192





theorem in1088_two_four_shores_external_opposite_impossible
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y z : V) (hxy : x ≠ y) (S A B U W : Finset V)
    (hA : A ⊆ S) (hW : W ⊆ S) (hAcard : A.card=4) (hBcard : B.card=8)
    (hUcard : U.card=8) (hWcard : W.card=4) (hBS : (B ∩ S).card ≤ 2)
    (hxB : x ∉ B) (hyB : y ∉ B) (hzB : z ∈ B)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hzU : ∀ u ∈ U, H.Adj z u)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, H.Adj u w) : False := by
  classical
  have hAU : ¬ Disjoint A U := by
    intro hd
    have hsub : A ∪ U ⊆ H.neighborFinset z := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (H.mem_neighborFinset z a).mpr (hBA z hzB a ha)
      · exact (H.mem_neighborFinset z a).mpr (hzU a ha)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd,hAcard,hUcard] at hc
    have hm := hmax z
    omega
  have hi : (A ∩ U).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hAU
  obtain ⟨a,ha⟩ := hi
  have haA : a ∈ A := (Finset.mem_inter.mp ha).1
  have haU : a ∈ U := (Finset.mem_inter.mp ha).2
  have hxS : x ∉ S := by
    intro hx
    exact (hSxy x hx).1.ne rfl
  have hyS : y ∉ S := by
    intro hy
    exact (hSxy y hy).2.ne rfl
  have hxW : x ∉ W := fun h => hxS (hW h)
  have hyW : y ∉ W := fun h => hyS (hW h)
  have hBW : (B ∩ W).card ≤ 2 := by
    have hsub : B ∩ W ⊆ B ∩ S := by
      intro b hb
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1,hW (Finset.mem_inter.mp hb).2⟩
    exact le_trans (Finset.card_le_card hsub) hBS
  have hBU := Finset.card_union_add_card_inter B W
  have hBUlow : 10 ≤ (B ∪ W).card := by omega
  have hxBU : x ∉ B ∪ W := by simp [hxB,hxW]
  have hyBU : y ∉ B ∪ W := by simp [hyB,hyW]
  have hxnot : x ∉ insert y (B ∪ W) := by simp [hxy,hxBU]
  have hsub : insert x (insert y (B ∪ W)) ⊆ H.neighborFinset a := by
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_union] at hb
    rcases hb with rfl | rfl | hb | hb
    · simpa using (hSxy a (hA haA)).1
    · simpa using (hSxy a (hA haA)).2
    · simpa using (hBA b hb a haA).symm
    · simpa using hUW a haU b hb
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyBU] at hc
  have hm := hmax a
  omega



theorem in1088_four_shore_forces_other_opposite_avoids_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B U W : Finset V)
    (hA : A ⊆ S) (hW : W ⊆ S) (hBcard : B.card=8)
    (hWcard : 4 ≤ W.card) (hBS : (B ∩ S).card ≤ 2)
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, H.Adj u w) : Disjoint A U := by
  classical
  apply Finset.disjoint_left.mpr
  intro a haA haU
  have hxS : x ∉ S := by
    intro hx
    exact (hSxy x hx).1.ne rfl
  have hyS : y ∉ S := by
    intro hy
    exact (hSxy y hy).2.ne rfl
  have hxW : x ∉ W := fun h => hxS (hW h)
  have hyW : y ∉ W := fun h => hyS (hW h)
  have hBW : (B ∩ W).card ≤ 2 := by
    have hsub : B ∩ W ⊆ B ∩ S := by
      intro b hb
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1,hW (Finset.mem_inter.mp hb).2⟩
    exact le_trans (Finset.card_le_card hsub) hBS
  have hBU := Finset.card_union_add_card_inter B W
  have hBUlow : 10 ≤ (B ∪ W).card := by omega
  have hxBU : x ∉ B ∪ W := by simp [hxB,hxW]
  have hyBU : y ∉ B ∪ W := by simp [hyB,hyW]
  have hxnot : x ∉ insert y (B ∪ W) := by simp [hxy,hxBU]
  have hsub : insert x (insert y (B ∪ W)) ⊆ H.neighborFinset a := by
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_union] at hb
    rcases hb with rfl | rfl | hb | hb
    · simpa using (hSxy a (hA haA)).1
    · simpa using (hSxy a (hA haA)).2
    · simpa using (hBA b hb a haA).symm
    · simpa using hUW a haU b hb
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyBU] at hc
  have hm := hmax a
  omega




theorem in1088_d11_disjoint_opposite_shore_has_no_opposite_neighbors
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V) (z₀ e : V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hE : 6 ≤ (B ∩ C).card) (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (he : e ∈ B ∩ C)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hBA : ∀ e ∈ B ∩ C, ∀ a ∈ A, H.Adj e a)
    (hWe : W e = S \ A) :
    ∀ q ∈ B ∩ C, ¬ H.Adj e q := by
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
  have hrootnotB : z₀ ∉ B := by
    intro hzB
    have hzQ0 : z₀ ∈ Q z₀ := hQ₀.symm ▸ hzB
    exact (hzQ z₀ hz₀ z₀ hzQ0).ne rfl
  have heC : e ∈ C := (Finset.mem_inter.mp he).2
  have heB : e ∈ B := (Finset.mem_inter.mp he).1
  have heroot : e ≠ z₀ := fun h => hrootnotB (h ▸ heB)
  have hrootedge : H.Adj e z₀ := (hzQ z₀ hz₀ e (hQ₀.symm ▸ heB)).symm
  have hEsub : B ∩ C ⊆ H.neighborFinset z₀ := by
    intro q hq
    exact (H.mem_neighborFinset z₀ q).mpr (hzQ z₀ hz₀ q (hQ₀.symm ▸ (Finset.mem_inter.mp hq).1))
  have hQeC : Q e ⊆ C := by
    intro q hq
    rcases Finset.mem_union.mp (hQ e heC hq) with hqS | hqC
    · by_cases hqA : q ∈ A
      · exact ((Finset.disjoint_left.mp (havoid e heC)) hqA hq).elim
      · have hqD : q ∈ D := Finset.mem_sdiff.mpr ⟨hqS,hqA⟩
        have hqW : q ∈ W e := hWe.symm ▸ hqD
        exact ((Finset.disjoint_left.mp (hdis e heC)) hq hqW).elim
    · exact hqC
  have hQesize : (Q e).card=6 := by
    have hs := hsize e heC
    rw [hWe] at hs
    change (Q e).card + D.card = 12 at hs
    omega
  have hrootnotQ : z₀ ∉ Q e := by
    intro hzQe
    have hDsub : D ⊆ H.neighborFinset z₀ := by
      intro a ha
      exact (H.mem_neighborFinset z₀ a).mpr (hcross e heC z₀ hzQe a (hWe.symm ▸ ha))
    have hd : Disjoint D (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hDC) ha (Finset.mem_inter.mp hb).2
    have hc := Finset.card_le_card (Finset.union_subset hDsub hEsub)
    rw [Finset.card_union_of_disjoint hd,hDsize] at hc
    have hm := hmax z₀
    omega
  have hQeE : Disjoint (Q e) (B ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro q hqQ hqE
    have hqS : S ⊆ H.neighborFinset q := by
      intro s hs
      by_cases hsA : s ∈ A
      · exact (H.mem_neighborFinset q s).mpr (hBA q hqE s hsA)
      · have hsD : s ∈ D := Finset.mem_sdiff.mpr ⟨hs,hsA⟩
        exact (H.mem_neighborFinset q s).mpr (hcross e heC q hqQ s (hWe.symm ▸ hsD))
    have heS : e ∉ S := fun h => (Finset.disjoint_left.mp hSC) h heC
    have hrS : z₀ ∉ S := fun h => (Finset.disjoint_left.mp hSC) h hz₀
    have henot : e ∉ insert z₀ S := by simp [heroot,heS]
    have hqe : H.Adj q e := (hzQ e heC q hqQ).symm
    have hqr : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ (Finset.mem_inter.mp hqE).1)).symm
    have hsub : insert e (insert z₀ S) ⊆ H.neighborFinset q := by
      intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · simpa using hqe
      · simpa using hqr
      · exact hqS hv
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem henot,Finset.card_insert_of_notMem hrS,hS] at hc
    have hm := hmax q
    omega
  intro q hqE heq
  have hAQ : Disjoint A (Q e) := havoid e heC
  have hrootA : z₀ ∉ A := fun h => (Finset.disjoint_left.mp hSC) (hA h) hz₀
  have hrootnot : z₀ ∉ A ∪ Q e := by simp [hrootA,hrootnotQ]
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqA : q ∉ A := fun h => (Finset.disjoint_left.mp hSC) (hA h) hqC
  have hqQ : q ∉ Q e := fun h => (Finset.disjoint_left.mp hQeE) h hqE
  have hqroot : q ≠ z₀ := fun h => hrootnotB (h ▸ (Finset.mem_inter.mp hqE).1)
  have hqnot : q ∉ insert z₀ (A ∪ Q e) := by simp [hqroot,hqA,hqQ]
  have hsub : insert q (insert z₀ (A ∪ Q e)) ⊆ H.neighborFinset e := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_union] at ha
    rcases ha with rfl | rfl | ha | ha
    · simpa using heq
    · simpa using hrootedge
    · simpa using hBA e he a ha
    · simpa using hzQ e heC a ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqnot,Finset.card_insert_of_notMem hrootnot,
    Finset.card_union_of_disjoint hAQ,hAcard,hQesize] at hc
  have hm := hmax e
  omega




theorem in1088_d11_eight_shore_cannot_target_nested_opposite
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y z₀ z q : V) (hxy : x ≠ y) (S C B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hB : B ⊆ S ∪ C) (hBS : (B ∩ S).card ≤ 2)
    (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (hz : z ∈ C) (hqE : q ∈ B ∩ C)
    (hqQz : q ∈ Q z) (hWz8 : (W z).card=8) (hQqB : Q q ⊆ B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y)
    (hW : ∀ v ∈ C, W v ⊆ S) (hsize : ∀ v ∈ C, (Q v).card+(W v).card=12)
    (hQ4 : ∀ v ∈ C, 4 ≤ (Q v).card)
    (hzQ : ∀ v ∈ C, ∀ u ∈ Q v, H.Adj v u)
    (hcross : ∀ v ∈ C, ∀ u ∈ Q v, ∀ w ∈ W v, H.Adj u w) : False := by
  classical
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqB : q ∈ B := (Finset.mem_inter.mp hqE).1
  have hrootnotB : z₀ ∉ B := by
    intro h
    exact (hzQ z₀ hz₀ z₀ (hQ₀.symm ▸ h)).ne rfl
  have hqroot : q ≠ z₀ := fun h => hrootnotB (h ▸ hqB)
  have hrootQq : z₀ ∉ Q q := fun h => hrootnotB (hQqB h)
  have hWqC : Disjoint (W z) C := by
    apply Finset.disjoint_left.mpr
    intro w hw hc
    exact (Finset.disjoint_left.mp hSC) (hW z hz hw) hc
  have hrootW : z₀ ∉ W z := fun h => (Finset.disjoint_left.mp hWqC) h hz₀
  have hQqCbound : (Q q ∩ C).card ≤ 2 := by
    have hdis : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWqC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ (W z ∪ (Q q ∩ C)) := by simp [hrootW,hrootQq]
    have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
    have hsub : insert z₀ (W z ∪ (Q q ∩ C)) ⊆ H.neighborFinset q := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
      rcases ha with rfl | ha | ⟨ha,_⟩
      · simpa using hrootedge
      · simpa using hcross z hz q hqQz a ha
      · simpa using hzQ q hqC a ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hdis,hWz8] at hc
    have hm := hmax q
    omega
  have hQqSbound : (Q q ∩ S).card ≤ 2 := by
    have hs : Q q ∩ S ⊆ B ∩ S := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨hQqB (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
    exact le_trans (Finset.card_le_card hs) hBS
  have hsplit : (Q q ∩ S).card + (Q q ∩ C).card = (Q q).card := by
    have hd : Disjoint (Q q ∩ S) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (Q q ∩ S) ∪ (Q q ∩ C) = Q q := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB (hQqB ha)) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQqsize : (Q q).card=4 := by have hq4 := hQ4 q hqC; omega
  have hWq8 : (W q).card=8 := by have hs := hsize q hqC; omega
  have hpos : 0 < (Q q ∩ S).card := by omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hpos
  have hbQ : b ∈ Q q := (Finset.mem_inter.mp hb).1
  have hbS : b ∈ S := (Finset.mem_inter.mp hb).2
  have hbB : b ∈ B := hQqB hbQ
  have hxS : x ∉ S := by intro h; exact (hSxy x h).1.ne rfl
  have hyS : y ∉ S := by intro h; exact (hSxy y h).2.ne rfl
  have hxW : x ∉ W q := fun h => hxS (hW q hqC h)
  have hyW : y ∉ W q := fun h => hyS (hW q hqC h)
  have hrW : z₀ ∉ W q := fun h => (Finset.disjoint_left.mp hSC) (hW q hqC h) hz₀
  have hqW : q ∉ W q := fun h => (Finset.disjoint_left.mp hSC) (hW q hqC h) hqC
  have hxroot : x ≠ z₀ := fun h => hxC (h ▸ hz₀)
  have hyroot : y ≠ z₀ := fun h => hyC (h ▸ hz₀)
  have hxq : x ≠ q := fun h => hxC (h ▸ hqC)
  have hyq : y ≠ q := fun h => hyC (h ▸ hqC)
  have hrootq : z₀ ≠ q := hqroot.symm
  have hxnot : x ∉ insert y (insert z₀ (insert q (W q))) := by simp [hxy,hxroot,hxq,hxW]
  have hynot : y ∉ insert z₀ (insert q (W q)) := by simp [hyroot,hyq,hyW]
  have hrnot : z₀ ∉ insert q (W q) := by simp [hrootq,hrW]
  have hbx : H.Adj b x := (hSxy b hbS).1
  have hby : H.Adj b y := (hSxy b hbS).2
  have hbr : H.Adj b z₀ := (hzQ z₀ hz₀ b (hQ₀.symm ▸ hbB)).symm
  have hbq : H.Adj b q := (hzQ q hqC b hbQ).symm
  have hsub : insert x (insert y (insert z₀ (insert q (W q)))) ⊆ H.neighborFinset b := by
    intro a ha
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | rfl | rfl | rfl | ha
    · simpa using hbx
    · simpa using hby
    · simpa using hbr
    · simpa using hbq
    · simpa using hcross q hqC b hbQ a ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hynot,
    Finset.card_insert_of_notMem hrnot,Finset.card_insert_of_notMem hqW,hWq8] at hc
  have hm := hmax b
  omega




theorem in1088_d11_six_shore_cannot_target_nested_six
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (z₀ z q : V) (S C B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hB : B ⊆ S ∪ C) (hBcard : B.card=8)
    (hBS : (B ∩ S).card ≤ 2)
    (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (hzE : z ∈ B ∩ C) (hqE : q ∈ B ∩ C)
    (hqQz : q ∈ Q z) (hWz6 : (W z).card=6) (hWq6 : (W q).card=6)
    (hQzB : Q z ⊆ B) (hQqB : Q q ⊆ B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hW : ∀ v ∈ C, W v ⊆ S) (hdis : ∀ v ∈ C, Disjoint (Q v) (W v))
    (hsize : ∀ v ∈ C, (Q v).card+(W v).card=12)
    (hzQ : ∀ v ∈ C, ∀ u ∈ Q v, H.Adj v u)
    (hcross : ∀ v ∈ C, ∀ u ∈ Q v, ∀ w ∈ W v, H.Adj u w) : False := by
  classical
  have hzC : z ∈ C := (Finset.mem_inter.mp hzE).2
  have hzB : z ∈ B := (Finset.mem_inter.mp hzE).1
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqB : q ∈ B := (Finset.mem_inter.mp hqE).1
  have hrootnotB : z₀ ∉ B := by
    intro h
    exact (hzQ z₀ hz₀ z₀ (hQ₀.symm ▸ h)).ne rfl
  have hrootQq : z₀ ∉ Q q := fun h => hrootnotB (hQqB h)
  have hWzC : Disjoint (W z) C := by
    apply Finset.disjoint_left.mpr
    intro w hw hc
    exact (Finset.disjoint_left.mp hSC) (hW z hzC hw) hc
  have hrootW : z₀ ∉ W z := fun h => (Finset.disjoint_left.mp hWzC) h hz₀
  have hQqsize : (Q q).card=6 := by have hs := hsize q hqC; omega
  have hQzsize : (Q z).card=6 := by have hs := hsize z hzC; omega
  have hQqCbound : (Q q ∩ C).card ≤ 4 := by
    have hd : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWzC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ W z ∪ (Q q ∩ C) := by simp [hrootW,hrootQq]
    have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
    have hsub : insert z₀ (W z ∪ (Q q ∩ C)) ⊆ H.neighborFinset q := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
      rcases ha with rfl | ha | ⟨ha,_⟩
      · simpa using hrootedge
      · simpa using hcross z hzC q hqQz a ha
      · simpa using hzQ q hqC a ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hd,hWz6] at hc
    have hm := hmax q
    omega
  have hQqSsub : Q q ∩ S ⊆ B ∩ S := by
    intro a ha
    exact Finset.mem_inter.mpr ⟨hQqB (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
  have hQqSbound : (Q q ∩ S).card ≤ 2 := le_trans (Finset.card_le_card hQqSsub) hBS
  have hsplit (T : Finset V) (hTB : T ⊆ B) : (T ∩ S).card+(T ∩ C).card=T.card := by
    have hd : Disjoint (T ∩ S) (T ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (T ∩ S) ∪ (T ∩ C) = T := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB (hTB ha)) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQsplit := hsplit (Q q) hQqB
  have hBsplit := hsplit B (Finset.Subset.rfl)
  have hQqCsize : (Q q ∩ C).card=4 := by omega
  have hQqSP := Finset.card_le_card hQqSsub
  have hPsize : (B ∩ S).card=2 := by omega
  have hEsize : (B ∩ C).card=6 := by omega
  have hPsub : B ∩ S ⊆ Q q := by
    have heq : Q q ∩ S = B ∩ S := Finset.eq_of_subset_of_card_le hQqSsub (by omega)
    intro a ha
    exact (Finset.mem_inter.mp (heq.symm ▸ ha)).1
  let N := insert z₀ (W z ∪ (Q q ∩ C))
  have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
  have hNsub : N ⊆ H.neighborFinset q := by
    intro a ha
    dsimp [N] at ha
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
    rcases ha with rfl | ha | ⟨ha,_⟩
    · simpa using hrootedge
    · simpa using hcross z hzC q hqQz a ha
    · simpa using hzQ q hqC a ha
  have hNsize : N.card=11 := by
    have hd : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWzC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ W z ∪ (Q q ∩ C) := by simp [hrootW,hrootQq]
    dsimp [N]
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hd,hWz6,hQqCsize]
  have hNeq : N = H.neighborFinset q := Finset.eq_of_subset_of_card_le hNsub (by rw [hNsize]; exact hmax q)
  have hP_W : B ∩ S ⊆ W z := by
    intro a ha
    have haQ : a ∈ Q q := hPsub ha
    have haN : a ∈ N := hNeq.symm ▸ ((H.mem_neighborFinset q a).mpr (hzQ q hqC a haQ))
    have haS : a ∈ S := (Finset.mem_inter.mp ha).2
    have haC : a ∉ C := fun h => (Finset.disjoint_left.mp hSC) haS h
    dsimp [N] at haN
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at haN
    rcases haN with heq | hw | ⟨_,hc⟩
    · exact (haC (heq ▸ hz₀)).elim
    · exact hw
    · exact (haC hc).elim
  have hQzE : Q z ⊆ B ∩ C := by
    intro a ha
    refine Finset.mem_inter.mpr ⟨hQzB ha,?_⟩
    rcases Finset.mem_union.mp (hB (hQzB ha)) with haS | haC
    · have haP : a ∈ B ∩ S := Finset.mem_inter.mpr ⟨hQzB ha,haS⟩
      exact ((Finset.disjoint_left.mp (hdis z hzC)) ha (hP_W haP)).elim
    · exact haC
  have hznotQ : z ∉ Q z := by
    intro h
    exact (hzQ z hzC z h).ne rfl
  have hsub : Q z ⊆ (B ∩ C).erase z := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨fun h => hznotQ (h ▸ ha),hQzE ha⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hzE,hQzsize,hEsize] at hc
  omega




theorem in1088_d11_saturated_opposite_target_impossible
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hB : B ⊆ S ∪ C) (hBcard : B.card=8) (hBS : (B ∩ S).card ≤ 2)
    (hE : 6 ≤ (B ∩ C).card) (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B)
    (hEsat : ∀ q ∈ B ∩ C, ∀ w ∈ S \ A, ¬ H.Adj q w) :
    ∀ t ∈ C, (∀ w ∈ S \ A, H.Adj t w) → False := by
  classical
  intro t ht htD
  let D := S \ A
  have hDsize : D.card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    dsimp [D]
    omega
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_sdiff.mp ha).1 hc
  have hDsub : D ⊆ H.neighborFinset t := by
    intro w hw
    exact (H.mem_neighborFinset t w).mpr (htD w hw)
  have hNbound : ((H.neighborFinset t) ∩ C).card ≤ 5 := by
    have hd : Disjoint D ((H.neighborFinset t) ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hDC) ha (Finset.mem_inter.mp hb).2
    have hs : D ∪ ((H.neighborFinset t) ∩ C) ⊆ H.neighborFinset t := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hDsub ha
      · exact (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd,hDsize] at hc
    have hm := hmax t
    omega
  have hQCS : (Q t ∩ S).card + (Q t ∩ C).card = (Q t).card := by
    have hd : Disjoint (Q t ∩ S) (Q t ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (Q t ∩ S) ∪ (Q t ∩ C) = Q t := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hQ t ht ha) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQtC : (Q t ∩ C).card ≤ 5 := by
    have hs : Q t ∩ C ⊆ (H.neighborFinset t) ∩ C := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨by simpa using hzQ t ht a (Finset.mem_inter.mp ha).1,
        (Finset.mem_inter.mp ha).2⟩
    exact le_trans (Finset.card_le_card hs) hNbound
  by_cases hAW : (A ∩ W t).Nonempty
  · obtain ⟨hAWsub,hQB⟩ := hnest t ht hAW
    have hQinE : (Q t ∩ (B ∩ C)).Nonempty := by
      by_contra hn
      have hQno : ∀ q ∈ Q t, q ∉ C := by
        intro q hq hqc
        apply hn
        exact ⟨q,Finset.mem_inter.mpr ⟨hq,Finset.mem_inter.mpr ⟨hQB hq,hqc⟩⟩⟩
      have hs : Q t ⊆ B ∩ S := by
        intro q hq
        refine Finset.mem_inter.mpr ⟨hQB hq,?_⟩
        rcases Finset.mem_union.mp (hQ t ht hq) with hs | hc
        · exact hs
        · exact ((hQno q hq) hc).elim
      have hc := Finset.card_le_card hs
      have hq4 := hQ4 t ht
      omega
    obtain ⟨q,hq⟩ := hQinE
    have hqQ : q ∈ Q t := (Finset.mem_inter.mp hq).1
    have hqE : q ∈ B ∩ C := (Finset.mem_inter.mp hq).2
    have hWsub : W t ⊆ A := by
      intro w hw
      by_contra hn
      have hwD : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hW t ht hw,hn⟩
      exact hEsat q hqE w hwD (hcross t ht q hqQ w hw)
    have hWeq : W t = A := Finset.Subset.antisymm hWsub hAWsub
    have hQsize : (Q t).card = 8 := by
      have hs := hsize t ht
      rw [hWeq,hAcard] at hs
      omega
    have hQeq : Q t = B := Finset.eq_of_subset_of_card_le hQB (by omega)
    have hEsub : B ∩ C ⊆ H.neighborFinset t := by
      intro q hq
      have hqQ : q ∈ Q t := hQeq.symm ▸ (Finset.mem_inter.mp hq).1
      exact (H.mem_neighborFinset t q).mpr (hzQ t ht q hqQ)
    have hde : Disjoint D (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro w hw he
      exact (Finset.disjoint_left.mp hDC) hw (Finset.mem_inter.mp he).2
    have hsub : D ∪ (B ∩ C) ⊆ H.neighborFinset t := Finset.union_subset hDsub hEsub
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hde,hDsize] at hc
    have hm := hmax t
    omega
  · have hdisAW : Disjoint A (W t) := by
      apply Finset.disjoint_left.mpr
      intro a ha hw
      exact hAW ⟨a,Finset.mem_inter.mpr ⟨ha,hw⟩⟩
    have hdisQW : Disjoint (Q t ∩ S) (W t) := by
      apply Finset.disjoint_left.mpr
      intro a ha hw
      exact (Finset.disjoint_left.mp (hdis t ht)) (Finset.mem_inter.mp ha).1 hw
    have hsub : (Q t ∩ S) ∪ W t ⊆ D := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp ha).2,?_⟩
        intro haA
        exact (Finset.disjoint_left.mp (havoid t ht)) haA (Finset.mem_inter.mp ha).1
      · refine Finset.mem_sdiff.mpr ⟨hW t ht ha,?_⟩
        intro haA
        exact (Finset.disjoint_left.mp hdisAW) haA ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisQW,hDsize] at hc
    have hs := hsize t ht
    omega


theorem in1088_d11_all_opposite_shores_disjoint_saturates
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


theorem in1088_d11_all_opposite_shores_cannot_be_disjoint
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
  have hEsat := in1088_d11_all_opposite_shores_disjoint_saturates H S C A B Q W z₀
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
  exact in1088_d11_saturated_opposite_target_impossible H S C A B Q W
    hSC hS hA hAcard hB hBcard hBS hE hmax hQ hW hdis hsize hQ4 havoid hzQ hcross hnest hEsat t htC htD


theorem in1088_d11_nested_first_four_shore_impossible
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
    exact in1088_two_four_shores_external_opposite_impossible H x y e hxy S A B (Q e) (W e)
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
    · have hno := in1088_d11_disjoint_opposite_shore_has_no_opposite_neighbors H S C A B Q W z₀ q
        hSC hS hA hAcard hE hz₀ hQ₀ hqE hmax hQ hdis hsize havoid hzQ hcross hBA hd
      have heC : e ∈ C := (Finset.mem_inter.mp he).2
      exact (hno e he (hzQ e heC q hqQ).symm).elim
    · exact ⟨q,hq,hn⟩
  have hno8 : ∀ e ∈ B ∩ C, A ⊆ W e → Q e ⊆ B → (W e).card ≠ 8 := by
    intro e he hAW hQB hw8
    obtain ⟨q,hq,hAq,hQq⟩ := htargetnested e he hQB
    exact in1088_d11_eight_shore_cannot_target_nested_opposite H x y z₀ e q hxy S C B Q W
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
      exact (in1088_d11_six_shore_cannot_target_nested_six H z₀ e q S C B Q W
        hSC hB hBcard hBS hz₀ hQ₀ he hqE (Finset.mem_inter.mp hq).1 hw6 hqw6
        hQB hQq hmax hW hdis hsize hzQ hcross).elim
  exact in1088_d11_all_opposite_shores_cannot_be_disjoint H S C A B Q W z₀
    hSC hS hA hAcard hB hBcard hBS hE hz₀ hQ₀ hmax hQ hW hdis hsize hQ4 havoid hzQ hcross hnest hBA hED




theorem in1088_external_neighbor_count_at_most_degree_sub_three
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y w q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hw : w ∈ S)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y) (hqw : H.Adj q w)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hqtype : q ∈ S ∨ (q ∈ C ∧ 3 ≤ ((H.neighborFinset q) ∩ S).card)) :
    ((H.neighborFinset q) ∩ C).card ≤ d-3 := by
  classical
  rcases hqtype with hqS | ⟨hqC,hqS3⟩
  · let U := (H.neighborFinset q) ∩ C
    have hwC : w ∉ C := fun h => (Finset.disjoint_left.mp hSC) hw h
    have hxU : x ∉ U := by simp [U,hxC]
    have hyU : y ∉ U := by simp [U,hyC]
    have hwU : w ∉ U := by simp [U,hwC]
    have hxw : x ≠ w := (hSxy w hw).1.ne.symm
    have hyw : y ≠ w := (hSxy w hw).2.ne.symm
    have hxnot : x ∉ insert y (insert w U) := by simp [hxy,hxw,hxU]
    have hynot : y ∉ insert w U := by simp [hyw,hyU]
    have hsub : insert x (insert y (insert w U)) ⊆ H.neighborFinset q := by
      intro a ha
      rw [H.mem_neighborFinset]
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | rfl | rfl | ha
      · exact (hSxy q hqS).1
      · exact (hSxy q hqS).2
      · exact hqw
      · exact (H.mem_neighborFinset q a).mp (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hynot,
      Finset.card_insert_of_notMem hwU] at hc
    have hc' := le_trans hc hmax
    dsimp [U] at hc'
    omega
  · let A := (H.neighborFinset q) ∩ S
    let B := (H.neighborFinset q) ∩ C
    have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have hsub : A ∪ B ⊆ H.neighborFinset q := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_inter.mp ha).1
      · exact (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hc
    have hc' := le_trans hc hmax
    dsimp [A,B] at hc'
    omega

open scoped BigOperators


theorem in1088_bridge_opposite_shore_two_external {V : Type*} [DecidableEq V]
    (S C Q W : Finset V) (d : ℕ) (hSC : Disjoint S C) (hQW : Disjoint Q W)
    (hQ : Q ⊆ S ∪ C) (hW : W ⊆ S) (hS : S.card+1=d)
    (hsize : Q.card+W.card=d+1) : 2 ≤ (Q ∩ C).card := by
  classical
  have hQSpart : Disjoint (Q ∩ S) W := by
    apply Finset.disjoint_left.mpr
    intro a ha hw
    exact (Finset.disjoint_left.mp hQW) (Finset.mem_inter.mp ha).1 hw
  have hQSunion : Q ∩ S ∪ W ⊆ S := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_inter.mp ha).2
    · exact hW ha
  have hle := Finset.card_le_card hQSunion
  rw [Finset.card_union_of_disjoint hQSpart] at hle
  have hdis : Disjoint (Q ∩ S) (Q ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hunion : Q ∩ S ∪ Q ∩ C = Q := by
    ext a
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · intro h
      exact h.elim And.left And.left
    · intro ha
      rcases Finset.mem_union.mp (hQ ha) with hs | hc
      · exact Or.inl ⟨ha,hs⟩
      · exact Or.inr ⟨ha,hc⟩
  have hcard : (Q ∩ S).card + (Q ∩ C).card = Q.card := by
    have h := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdis] at h
    exact h
  omega


theorem in1088_external_neighbor_count_with_four_internal
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hfour : 4 ≤ ((H.neighborFinset q) ∩ S).card) :
    ((H.neighborFinset q) ∩ C).card + 4 ≤ d := by
  classical
  let A := (H.neighborFinset q) ∩ S
  let B := (H.neighborFinset q) ∩ C
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hsub : A ∪ B ⊆ H.neighborFinset q := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hc' := le_trans hc hmax
  dsimp [A,B] at hc'
  omega



theorem in1088_external_neighbor_count_with_r_internal
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (S C : Finset V) (d r : ℕ) (hSC : Disjoint S C)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hfour : r ≤ ((H.neighborFinset q) ∩ S).card) :
    ((H.neighborFinset q) ∩ C).card + r ≤ d := by
  classical
  let A := (H.neighborFinset q) ∩ S
  let B := (H.neighborFinset q) ∩ C
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hsub : A ∪ B ⊆ H.neighborFinset q := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hc' := le_trans hc hmax
  dsimp [A,B] at hc'
  omega




theorem in1088_choose_external_non_neighbor_padding {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (q : V) (S C : Finset V) (d r : ℕ)
    (hSC : Disjoint S C) (hr : 4 ≤ r) (hCr : d ≤ C.card)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hqin : r ≤ ((H.neighborFinset q) ∩ S).card) :
    ∃ P : Finset V, P ⊆ C \ H.neighborFinset q ∧ P.card = r-3 := by
  classical
  have hnc := in1088_external_neighbor_count_with_r_internal H q S C d r hSC hmax hqin
  let N := (H.neighborFinset q) ∩ C
  have hNsub : N ⊆ C := Finset.inter_subset_right
  have hc := Finset.card_sdiff_add_card_eq_card hNsub
  have hbound : r-3 ≤ (C \ N).card := by
    dsimp [N] at hc ⊢
    omega
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hbound
  refine ⟨P,?_,hcard⟩
  intro a ha
  have ha' := hP ha
  simp only [N,Finset.mem_sdiff,Finset.mem_inter,not_and] at ha' ⊢
  exact ⟨ha'.1, fun h => ha'.2 h ha'.1⟩

theorem in1088_bridge_family_variable_refined_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L r : ℕ) (hr : 4 ≤ r) (hCr : d ≤ C.card) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, r ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card * (Q z).card) :
    let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
    L * C.card + r*(r-3)*T.card ≤ (d-1)*(d-2)*(d-3) := by
  classical
  let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
  have hpads : ∀ q : V, ∃ P : Finset V, q ∈ T →
      P ⊆ C \ H.neighborFinset q ∧ P.card = r-3 := by
    intro q
    by_cases hq : q ∈ T
    · have hqin := (Finset.mem_filter.mp hq).2
      obtain ⟨P,hsub,hcard⟩ := in1088_choose_external_non_neighbor_padding H q S C d r hSC hr hCr (hmax q) hqin
      exact ⟨P,fun _ => ⟨hsub,hcard⟩⟩
    · exact ⟨∅,fun h => (hq h).elim⟩
  choose Pad hPad using hpads
  let Z : V → Finset V := fun q => if q ∈ T then ((H.neighborFinset q) ∩ C) ∪ Pad q else ((H.neighborFinset q) ∩ C)
  let D : V → Finset V := fun w => (((H.neighborFinset w).erase x).erase y).filter
    (fun q => q ∈ S ∨ q ∈ T)
  let upper : Finset ((V × V) × V) := S.biUnion fun w =>
    (D w).biUnion fun q => (Z q).image (fun z => ((w,q),z))
  have hupper : upper.card ≤ S.card * ((d-2)*(d-3)) := by
    dsimp [upper]
    apply Finset.card_biUnion_le_card_mul
    intro w hw
    have hx : x ∈ H.neighborFinset w := by simpa using (hSxy w hw).1
    have hy : y ∈ (H.neighborFinset w).erase x := by
      apply Finset.mem_erase.mpr
      exact ⟨hxy.symm, by simpa using (hSxy w hw).2⟩
    have hwcard : (D w).card ≤ d-2 := by
      have hfilter : (D w).card ≤ (((H.neighborFinset w).erase x).erase y).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_erase_of_mem hy,Finset.card_erase_of_mem hx] at hfilter
      have hm := hmax w
      have hxcard : 2 ≤ (H.neighborFinset w).card := by
        have hpair : ({x,y} : Finset V) ⊆ H.neighborFinset w := by
          intro a ha
          simp only [Finset.mem_insert,Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hx
          · exact Finset.mem_of_mem_erase hy
        have hc := Finset.card_le_card hpair
        rw [Finset.card_pair hxy] at hc
        exact hc
      omega
    have hinner : ∀ q ∈ D w, ((Z q).image (fun z => ((w,q),z))).card ≤ d-3 := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqN := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'.1)
      have hqw : H.Adj q w := by
        have h : H.Adj w q := by simpa using hqN
        exact h.symm
      have hZ : (Z q).card ≤ d-3 := by
        by_cases hqT : q ∈ T
        · have hqin := (Finset.mem_filter.mp hqT).2
          have hc := in1088_external_neighbor_count_with_r_internal H q S C d r hSC (hmax q) hqin
          obtain ⟨hpsub,hpcard⟩ := hPad q hqT
          have hd : Disjoint ((H.neighborFinset q) ∩ C) (Pad q) := by
            apply Finset.disjoint_left.mpr
            intro a ha hp
            have hp' := hpsub hp
            exact (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mp ha).1
          dsimp [Z]
          rw [if_pos hqT,Finset.card_union_of_disjoint hd,hpcard]
          omega
        · have hqS : q ∈ S := by
            rcases hq'.2 with hs | ht
            · exact hs
            · exact (hqT ht).elim
          have hqtype : q ∈ S ∨ (q ∈ C ∧ 3 ≤ ((H.neighborFinset q) ∩ S).card) := Or.inl hqS
          have hc := in1088_external_neighbor_count_at_most_degree_sub_three H x y w q hxy S C d hSC hxC hyC hw hSxy hqw (hmax q) hqtype
          simpa [Z,hqT] using hc
      exact le_trans Finset.card_image_le hZ
    have hc := Finset.card_biUnion_le_card_mul (D w)
      (fun q => (Z q).image (fun z => ((w,q),z))) (d-3) hinner
    exact le_trans hc (Nat.mul_le_mul_right (d-3) hwcard)
  let lower : Finset ((V × V) × V) := C.biUnion fun z =>
    ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))
  have hitem : ∀ z, (((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))).card =
      (W z).card*(Q z).card := by
    intro z
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h),Finset.card_product]
  have hpairwise : (C : Set V).PairwiseDisjoint (fun z =>
      ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))) := by
    intro z hz z' hz' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg Prod.snd he).trans (congrArg Prod.snd he').symm
  have hlower : L * C.card ≤ lower.card := by
    dsimp [lower]
    rw [Finset.card_biUnion hpairwise]
    have hs : ∑ z ∈ C, L ≤ ∑ z ∈ C, (W z).card*(Q z).card := by
      apply Finset.sum_le_sum
      intro z hz
      exact hprod z hz
    simp only [hitem] at *
    simpa [Nat.mul_comm] using hs
  have hsub : lower ⊆ upper := by
    intro t ht
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hq⟩ := Finset.mem_product.mp hp
    have hwS : p.1 ∈ S := hW z hz hw
    have hqN : p.2 ∈ H.neighborFinset p.1 := by simpa using (hcross z hz p.2 hq p.1 hw).symm
    have hqx : p.2 ≠ x := fun he => hxQ z hz (he ▸ hq)
    have hqy : p.2 ≠ y := fun he => hyQ z hz (he ▸ hq)
    have hqgood : p.2 ∈ S ∨ p.2 ∈ T := by
      rcases Finset.mem_union.mp (hQ z hz hq) with hs | hc
      · exact Or.inl hs
      · right
        apply Finset.mem_filter.mpr
        refine ⟨hc, ?_⟩
        have hsub : W z ⊆ (H.neighborFinset p.2) ∩ S := by
          intro w hw'
          apply Finset.mem_inter.mpr
          exact ⟨by simpa using hcross z hz p.2 hq w hw', hW z hz hw'⟩
        have hle := Finset.card_le_card hsub
        have hm := hWmin z hz
        omega
    have hq' : p.2 ∈ D p.1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, hqgood⟩
    have hzN : z ∈ H.neighborFinset p.2 := by simpa using (hzQ z hz p.2 hq).symm
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨p.2,hq',?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    by_cases hpT : p.2 ∈ T
    · simp only [Z,if_pos hpT,Finset.mem_union]
      exact Or.inl (Finset.mem_inter.mpr ⟨hzN,hz⟩)
    · simp only [Z,if_neg hpT]
      exact Finset.mem_inter.mpr ⟨hzN,hz⟩
  let extra : Finset ((V × V) × V) := T.biUnion fun q =>
    (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))
  have heItem : ∀ q, ((((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))).card =
      ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
    intro q
    rw [Finset.card_image_of_injective _ (by intro a b h; cases a; cases b; simp_all), Finset.card_product]
  have hePair : (T : Set V).PairwiseDisjoint (fun q =>
      (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg (fun t : (V × V) × V => t.1.2) he).trans (congrArg (fun t : (V × V) × V => t.1.2) he').symm
  have hextra : r*(r-3)*T.card ≤ extra.card := by
    dsimp [extra]
    rw [Finset.card_biUnion hePair]
    have hs : ∑ q ∈ T, r*(r-3) ≤ ∑ q ∈ T, ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hqin := (Finset.mem_filter.mp hq).2
      have hp := (hPad q hq).2
      rw [hp]
      exact Nat.mul_le_mul_right (r-3) hqin
    simp only [heItem] at *
    simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hs
  have hextraSub : extra ⊆ upper := by
    intro t ht
    obtain ⟨q,hqT,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hz⟩ := Finset.mem_product.mp hp
    have hqC : q ∈ C := (Finset.mem_filter.mp hqT).1
    have hwS : p.1 ∈ S := (Finset.mem_inter.mp hw).2
    have hqw : H.Adj q p.1 := by simpa using (Finset.mem_inter.mp hw).1
    have hqN : q ∈ H.neighborFinset p.1 := by simpa using hqw.symm
    have hqx : q ≠ x := fun h => hxC (h ▸ hqC)
    have hqy : q ≠ y := fun h => hyC (h ▸ hqC)
    have hqD : q ∈ D p.1 := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, Or.inr hqT⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨q,hqD,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, ?_, rfl⟩
    simp only [Z,if_pos hqT,Finset.mem_union]
    exact Or.inr hz
  have hdisjoint : Disjoint lower extra := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hqT,ht'⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht'
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht
    have hpq : p'.2 = q := congrArg (fun t : (V × V) × V => t.1.2) (he'.trans he.symm)
    have hzp : z = p.2 := congrArg Prod.snd (he'.trans he.symm)
    have hpQ : p'.2 ∈ Q z := (Finset.mem_product.mp hp').2
    have hh := hzQ z hz p'.2 hpQ
    rw [hpq,hzp] at hh
    have hzPad : p.2 ∈ Pad q := (Finset.mem_product.mp hp).2
    have hzNot : p.2 ∉ H.neighborFinset q := (Finset.mem_sdiff.mp ((hPad q hqT).1 hzPad)).2
    exact hzNot (by simpa using hh.symm)
  have hunion : lower ∪ extra ⊆ upper := Finset.union_subset hsub hextraSub
  have hcount := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisjoint] at hcount
  have hbound : L*C.card + r*(r-3)*T.card ≤ S.card*((d-2)*(d-3)) := by
    have := hupper
    omega
  have hS : S.card = d-1 := by omega
  rw [hS] at hbound
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbound

theorem in1088_internal_neighbor_budget
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hq : q ∈ S)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hmax : (H.neighborFinset q).card ≤ d) :
    ((H.neighborFinset q) ∩ S).card + ((H.neighborFinset q) ∩ C).card + 2 ≤ d := by
  classical
  let A := (H.neighborFinset q) ∩ S
  let B := (H.neighborFinset q) ∩ C
  have hxS : x ∉ S := by
    intro hx
    exact (hSxy x hx).1.ne rfl
  have hyS : y ∉ S := by
    intro hy
    exact (hSxy y hy).2.ne rfl
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hxAB : x ∉ A ∪ B := by simp [A,B,hxS,hxC]
  have hyAB : y ∉ A ∪ B := by simp [A,B,hyS,hyC]
  have hxnot : x ∉ insert y (A ∪ B) := by simp [hxy,hxAB]
  have hsub : insert x (insert y (A ∪ B)) ⊆ H.neighborFinset q := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_union] at ha
    rcases ha with rfl | rfl | ha | ha
    · simpa using (hSxy q hq).1
    · simpa using (hSxy q hq).2
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyAB,
      Finset.card_union_of_disjoint hd] at hc
  have := le_trans hc hmax
  dsimp [A,B] at *
  omega

theorem in1088_choose_internal_non_neighbor_padding
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hq : q ∈ S) (hCsize : d ≤ C.card)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hmax : (H.neighborFinset q).card ≤ d) :
    ∃ P : Finset V, P ⊆ C \ H.neighborFinset q ∧
      P.card = ((H.neighborFinset q) ∩ S).card-1 := by
  classical
  have hbudget := in1088_internal_neighbor_budget H x y q hxy S C d hSC hxC hyC hq hSxy hmax
  let N := (H.neighborFinset q) ∩ C
  have hNsub : N ⊆ C := Finset.inter_subset_right
  have hc := Finset.card_sdiff_add_card_eq_card hNsub
  have hbound : ((H.neighborFinset q) ∩ S).card-1 ≤ (C \ N).card := by
    dsimp [N] at hc ⊢
    omega
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hbound
  refine ⟨P,?_,hcard⟩
  intro a ha
  have ha' := hP ha
  simp only [N,Finset.mem_sdiff,Finset.mem_inter,not_and] at ha' ⊢
  exact ⟨ha'.1, fun h => ha'.2 h ha'.1⟩


theorem in1088_bridge_family_internal_external_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L r : ℕ) (hr : 4 ≤ r) (hCr : d ≤ C.card) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, r ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card * (Q z).card) :
    let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
    L * C.card + r*(r-3)*T.card + Finset.sum S (fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)) ≤ (d-1)*(d-2)*(d-3) := by
  classical
  let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
  have hpads : ∀ q : V, ∃ P : Finset V, q ∈ T →
      P ⊆ C \ H.neighborFinset q ∧ P.card = r-3 := by
    intro q
    by_cases hq : q ∈ T
    · have hqin := (Finset.mem_filter.mp hq).2
      obtain ⟨P,hsub,hcard⟩ := in1088_choose_external_non_neighbor_padding H q S C d r hSC hr hCr (hmax q) hqin
      exact ⟨P,fun _ => ⟨hsub,hcard⟩⟩
    · exact ⟨∅,fun h => (hq h).elim⟩
  choose Pad hPad using hpads
  have hpadsI : ∀ q : V, ∃ P : Finset V, q ∈ S →
      P ⊆ C \ H.neighborFinset q ∧ P.card = ((H.neighborFinset q) ∩ S).card - 1 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨P,hsub,hcard⟩ := in1088_choose_internal_non_neighbor_padding H x y q hxy S C d hSC hxC hyC hq hCr hSxy (hmax q)
      exact ⟨P,fun _ => ⟨hsub,hcard⟩⟩
    · exact ⟨∅,fun h => (hq h).elim⟩
  choose PadI hPadI using hpadsI
  have hTS : Disjoint T S := by
    apply Finset.disjoint_left.mpr
    intro q hqT hqS
    exact (Finset.disjoint_left.mp hSC) hqS (Finset.mem_filter.mp hqT).1
  let Z : V → Finset V := fun q => if q ∈ T then ((H.neighborFinset q) ∩ C) ∪ Pad q else if q ∈ S then ((H.neighborFinset q) ∩ C) ∪ PadI q else ((H.neighborFinset q) ∩ C)
  let D : V → Finset V := fun w => (((H.neighborFinset w).erase x).erase y).filter
    (fun q => q ∈ S ∨ q ∈ T)
  let upper : Finset ((V × V) × V) := S.biUnion fun w =>
    (D w).biUnion fun q => (Z q).image (fun z => ((w,q),z))
  have hupper : upper.card ≤ S.card * ((d-2)*(d-3)) := by
    dsimp [upper]
    apply Finset.card_biUnion_le_card_mul
    intro w hw
    have hx : x ∈ H.neighborFinset w := by simpa using (hSxy w hw).1
    have hy : y ∈ (H.neighborFinset w).erase x := by
      apply Finset.mem_erase.mpr
      exact ⟨hxy.symm, by simpa using (hSxy w hw).2⟩
    have hwcard : (D w).card ≤ d-2 := by
      have hfilter : (D w).card ≤ (((H.neighborFinset w).erase x).erase y).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_erase_of_mem hy,Finset.card_erase_of_mem hx] at hfilter
      have hm := hmax w
      have hxcard : 2 ≤ (H.neighborFinset w).card := by
        have hpair : ({x,y} : Finset V) ⊆ H.neighborFinset w := by
          intro a ha
          simp only [Finset.mem_insert,Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hx
          · exact Finset.mem_of_mem_erase hy
        have hc := Finset.card_le_card hpair
        rw [Finset.card_pair hxy] at hc
        exact hc
      omega
    have hinner : ∀ q ∈ D w, ((Z q).image (fun z => ((w,q),z))).card ≤ d-3 := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqN := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'.1)
      have hqw : H.Adj q w := by
        have h : H.Adj w q := by simpa using hqN
        exact h.symm
      have hZ : (Z q).card ≤ d-3 := by
        by_cases hqT : q ∈ T
        · have hqin := (Finset.mem_filter.mp hqT).2
          have hc := in1088_external_neighbor_count_with_r_internal H q S C d r hSC (hmax q) hqin
          obtain ⟨hpsub,hpcard⟩ := hPad q hqT
          have hd : Disjoint ((H.neighborFinset q) ∩ C) (Pad q) := by
            apply Finset.disjoint_left.mpr
            intro a ha hp
            have hp' := hpsub hp
            exact (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mp ha).1
          dsimp [Z]
          rw [if_pos hqT,Finset.card_union_of_disjoint hd,hpcard]
          omega
        · have hqS : q ∈ S := by
            rcases hq'.2 with hs | ht
            · exact hs
            · exact (hqT ht).elim
          have hc := in1088_internal_neighbor_budget H x y q hxy S C d hSC hxC hyC hqS hSxy (hmax q)
          have hspos : 1 ≤ ((H.neighborFinset q) ∩ S).card := by
            apply Finset.one_le_card.mpr
            exact ⟨w,Finset.mem_inter.mpr ⟨by simpa using hqw,hw⟩⟩
          obtain ⟨hpsub,hpcard⟩ := hPadI q hqS
          have hd : Disjoint ((H.neighborFinset q) ∩ C) (PadI q) := by
            apply Finset.disjoint_left.mpr
            intro a ha hp
            exact (Finset.mem_sdiff.mp (hpsub hp)).2 (Finset.mem_inter.mp ha).1
          dsimp [Z]
          rw [if_neg hqT,if_pos hqS,Finset.card_union_of_disjoint hd,hpcard]
          omega
      exact le_trans Finset.card_image_le hZ
    have hc := Finset.card_biUnion_le_card_mul (D w)
      (fun q => (Z q).image (fun z => ((w,q),z))) (d-3) hinner
    exact le_trans hc (Nat.mul_le_mul_right (d-3) hwcard)
  let lower : Finset ((V × V) × V) := C.biUnion fun z =>
    ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))
  have hitem : ∀ z, (((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))).card =
      (W z).card*(Q z).card := by
    intro z
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h),Finset.card_product]
  have hpairwise : (C : Set V).PairwiseDisjoint (fun z =>
      ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))) := by
    intro z hz z' hz' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg Prod.snd he).trans (congrArg Prod.snd he').symm
  have hlower : L * C.card ≤ lower.card := by
    dsimp [lower]
    rw [Finset.card_biUnion hpairwise]
    have hs : ∑ z ∈ C, L ≤ ∑ z ∈ C, (W z).card*(Q z).card := by
      apply Finset.sum_le_sum
      intro z hz
      exact hprod z hz
    simp only [hitem] at *
    simpa [Nat.mul_comm] using hs
  have hsub : lower ⊆ upper := by
    intro t ht
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hq⟩ := Finset.mem_product.mp hp
    have hwS : p.1 ∈ S := hW z hz hw
    have hqN : p.2 ∈ H.neighborFinset p.1 := by simpa using (hcross z hz p.2 hq p.1 hw).symm
    have hqx : p.2 ≠ x := fun he => hxQ z hz (he ▸ hq)
    have hqy : p.2 ≠ y := fun he => hyQ z hz (he ▸ hq)
    have hqgood : p.2 ∈ S ∨ p.2 ∈ T := by
      rcases Finset.mem_union.mp (hQ z hz hq) with hs | hc
      · exact Or.inl hs
      · right
        apply Finset.mem_filter.mpr
        refine ⟨hc, ?_⟩
        have hsub : W z ⊆ (H.neighborFinset p.2) ∩ S := by
          intro w hw'
          apply Finset.mem_inter.mpr
          exact ⟨by simpa using hcross z hz p.2 hq w hw', hW z hz hw'⟩
        have hle := Finset.card_le_card hsub
        have hm := hWmin z hz
        omega
    have hq' : p.2 ∈ D p.1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, hqgood⟩
    have hzN : z ∈ H.neighborFinset p.2 := by simpa using (hzQ z hz p.2 hq).symm
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨p.2,hq',?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    by_cases hpT : p.2 ∈ T
    · simp only [Z,if_pos hpT,Finset.mem_union]
      exact Or.inl (Finset.mem_inter.mpr ⟨hzN,hz⟩)
    · by_cases hpS : p.2 ∈ S
      · simp only [Z,if_neg hpT,if_pos hpS,Finset.mem_union]
        exact Or.inl (Finset.mem_inter.mpr ⟨hzN,hz⟩)
      · simp only [Z,if_neg hpT,if_neg hpS]
        exact Finset.mem_inter.mpr ⟨hzN,hz⟩
  let extra : Finset ((V × V) × V) := T.biUnion fun q =>
    (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))
  have heItem : ∀ q, ((((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))).card =
      ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
    intro q
    rw [Finset.card_image_of_injective _ (by intro a b h; cases a; cases b; simp_all), Finset.card_product]
  have hePair : (T : Set V).PairwiseDisjoint (fun q =>
      (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg (fun t : (V × V) × V => t.1.2) he).trans (congrArg (fun t : (V × V) × V => t.1.2) he').symm
  have hextra : r*(r-3)*T.card ≤ extra.card := by
    dsimp [extra]
    rw [Finset.card_biUnion hePair]
    have hs : ∑ q ∈ T, r*(r-3) ≤ ∑ q ∈ T, ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hqin := (Finset.mem_filter.mp hq).2
      have hp := (hPad q hq).2
      rw [hp]
      exact Nat.mul_le_mul_right (r-3) hqin
    simp only [heItem] at *
    simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hs
  have hextraSub : extra ⊆ upper := by
    intro t ht
    obtain ⟨q,hqT,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hz⟩ := Finset.mem_product.mp hp
    have hqC : q ∈ C := (Finset.mem_filter.mp hqT).1
    have hwS : p.1 ∈ S := (Finset.mem_inter.mp hw).2
    have hqw : H.Adj q p.1 := by simpa using (Finset.mem_inter.mp hw).1
    have hqN : q ∈ H.neighborFinset p.1 := by simpa using hqw.symm
    have hqx : q ≠ x := fun h => hxC (h ▸ hqC)
    have hqy : q ≠ y := fun h => hyC (h ▸ hqC)
    have hqD : q ∈ D p.1 := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, Or.inr hqT⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨q,hqD,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, ?_, rfl⟩
    simp only [Z,if_pos hqT,Finset.mem_union]
    exact Or.inr hz
  have hdisjoint : Disjoint lower extra := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hqT,ht'⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht'
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht
    have hpq : p'.2 = q := congrArg (fun t : (V × V) × V => t.1.2) (he'.trans he.symm)
    have hzp : z = p.2 := congrArg Prod.snd (he'.trans he.symm)
    have hpQ : p'.2 ∈ Q z := (Finset.mem_product.mp hp').2
    have hh := hzQ z hz p'.2 hpQ
    rw [hpq,hzp] at hh
    have hzPad : p.2 ∈ Pad q := (Finset.mem_product.mp hp).2
    have hzNot : p.2 ∉ H.neighborFinset q := (Finset.mem_sdiff.mp ((hPad q hqT).1 hzPad)).2
    exact hzNot (by simpa using hh.symm)
  let extraI : Finset ((V × V) × V) := S.biUnion fun q =>
    (((H.neighborFinset q) ∩ S) ×ˢ PadI q).image (fun p => ((p.1,q),p.2))
  have heIItem : ∀ q, ((((H.neighborFinset q) ∩ S) ×ˢ PadI q).image (fun p => ((p.1,q),p.2))).card =
      ((H.neighborFinset q) ∩ S).card*(PadI q).card := by
    intro q
    rw [Finset.card_image_of_injective _ (by intro a b h; cases a; cases b; simp_all), Finset.card_product]
  have heIPair : (S : Set V).PairwiseDisjoint (fun q =>
      (((H.neighborFinset q) ∩ S) ×ˢ PadI q).image (fun p => ((p.1,q),p.2))) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg (fun t : (V × V) × V => t.1.2) he).trans (congrArg (fun t : (V × V) × V => t.1.2) he').symm
  have hextraI : Finset.sum S (fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)) = extraI.card := by
    dsimp [extraI]
    rw [Finset.card_biUnion heIPair]
    apply Finset.sum_congr rfl
    intro q hq
    rw [heIItem,(hPadI q hq).2]
  have hextraISub : extraI ⊆ upper := by
    intro t ht
    obtain ⟨q,hqS,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hz⟩ := Finset.mem_product.mp hp
    have hqT : q ∉ T := fun h => (Finset.disjoint_left.mp hTS) h hqS
    have hwS : p.1 ∈ S := (Finset.mem_inter.mp hw).2
    have hqw : H.Adj q p.1 := by simpa using (Finset.mem_inter.mp hw).1
    have hqN : q ∈ H.neighborFinset p.1 := by simpa using hqw.symm
    have hqx : q ≠ x := (hSxy q hqS).1.ne
    have hqy : q ≠ y := (hSxy q hqS).2.ne
    have hqD : q ∈ D p.1 := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, Or.inl hqS⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨q,hqD,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, ?_, rfl⟩
    simp only [Z,if_neg hqT,if_pos hqS,Finset.mem_union]
    exact Or.inr hz
  have hdisjointI : Disjoint lower extraI := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hqS,ht'⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht'
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht
    have hpq : p'.2 = q := congrArg (fun t : (V × V) × V => t.1.2) (he'.trans he.symm)
    have hzp : z = p.2 := congrArg Prod.snd (he'.trans he.symm)
    have hpQ : p'.2 ∈ Q z := (Finset.mem_product.mp hp').2
    have hh := hzQ z hz p'.2 hpQ
    rw [hpq,hzp] at hh
    have hzPad : p.2 ∈ PadI q := (Finset.mem_product.mp hp).2
    have hzNot : p.2 ∉ H.neighborFinset q := (Finset.mem_sdiff.mp ((hPadI q hqS).1 hzPad)).2
    exact hzNot (by simpa using hh.symm)
  have hdisjointEI : Disjoint extra extraI := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hqT,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht
    obtain ⟨q',hqS,ht'⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht'
    have hqeq : q = q' := (congrArg (fun t : (V × V) × V => t.1.2) he).trans (congrArg (fun t : (V × V) × V => t.1.2) he').symm
    subst q'
    exact (Finset.disjoint_left.mp hTS) hqT hqS
  have hunion : (lower ∪ extra) ∪ extraI ⊆ upper := Finset.union_subset (Finset.union_subset hsub hextraSub) hextraISub
  have hcount := Finset.card_le_card hunion
  have hdisunion : Disjoint (lower ∪ extra) extraI := Finset.disjoint_union_left.mpr ⟨hdisjointI,hdisjointEI⟩
  rw [Finset.card_union_of_disjoint hdisunion,Finset.card_union_of_disjoint hdisjoint] at hcount
  have hbound : L*C.card + r*(r-3)*T.card + Finset.sum S (fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)) ≤ S.card*((d-2)*(d-3)) := by
    have := hupper
    omega
  have hS : S.card = d-1 := by omega
  rw [hS] at hbound
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbound


theorem in1088_complete_bipartite_internal_walk_charge
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S A B : Finset V) (hA : A ⊆ S) (hB : B ⊆ S) (hdis : Disjoint A B)
    (hAcard : A.card=4) (hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) :
    4*B.card*(B.card-1)+12*B.card ≤
      Finset.sum S (fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)) := by
  classical
  let f : V → ℕ := fun q => ((H.neighborFinset q) ∩ S).card * (((H.neighborFinset q) ∩ S).card-1)
  have hAs : ∀ a ∈ A, B.card ≤ ((H.neighborFinset a) ∩ S).card := by
    intro a ha
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_inter.mpr ⟨by simpa using hcross a ha b hb,hB hb⟩
  have hBs : ∀ b ∈ B, 4 ≤ ((H.neighborFinset b) ∩ S).card := by
    intro b hb
    have hs : A ⊆ (H.neighborFinset b) ∩ S := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨by simpa using (hcross a ha b hb).symm,hA ha⟩
    have hc := Finset.card_le_card hs
    omega
  have hAlow : A.card*(B.card*(B.card-1)) ≤ ∑ a ∈ A, f a := by
    have h := Finset.sum_le_sum (s := A) (f := fun _ => B.card*(B.card-1)) (g := f) (by
      intro a ha
      have hc := hAs a ha
      have hd := Nat.sub_le_sub_right hc 1
      exact Nat.mul_le_mul hc hd)
    simpa [Nat.mul_comm] using h
  have hBlow : B.card*12 ≤ ∑ b ∈ B, f b := by
    have h := Finset.sum_le_sum (s := B) (f := fun _ => 12) (g := f) (by
      intro b hb
      have hc := hBs b hb
      have hd := Nat.sub_le_sub_right hc 1
      have hh := Nat.mul_le_mul hc hd
      simpa using hh)
    simpa [Nat.mul_comm] using h
  have hsub : A ∪ B ⊆ S := Finset.union_subset hA hB
  have hsum : (A ∪ B).sum f ≤ S.sum f := Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_union hdis] at hsum
  dsimp [f] at *
  rw [hAcard] at hAlow
  simp only [Nat.mul_assoc] at hAlow ⊢
  omega


theorem in1088_bridge_family_variable_external_incidence_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S C : Finset V) (d r : ℕ) (hSC : Disjoint S C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, r ≤ (W z).card) :
    let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
    2*C.card ≤ (d-r)*T.card := by
  classical
  let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
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
      exact in1088_bridge_opposite_shore_two_external S C (Q z) (W z) d hSC
        (hdis z hz) (hQ z hz) (hW z hz) hSsize (hsize z hz)
    simp only [hitem] at *
    simpa [Nat.mul_comm] using hs
  let upper : Finset (V × V) := T.biUnion fun q =>
    ((H.neighborFinset q) ∩ C).image (fun z => (z,q))
  have hup : upper.card ≤ T.card*(d-r) := by
    dsimp [upper]
    apply Finset.card_biUnion_le_card_mul
    intro q hq
    have hq4 : r ≤ ((H.neighborFinset q) ∩ S).card := (Finset.mem_filter.mp hq).2
    have hc := in1088_external_neighbor_count_with_r_internal H q S C d r hSC (hmax q) hq4
    calc
      (((H.neighborFinset q) ∩ C).image (fun z => (z,q))).card ≤ ((H.neighborFinset q) ∩ C).card := Finset.card_image_le
      _ ≤ d-r := by omega
  have hsub : lower ⊆ upper := by
    intro t ht
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    have hqQ : q ∈ Q z := (Finset.mem_inter.mp hq).1
    have hqC : q ∈ C := (Finset.mem_inter.mp hq).2
    have hq4 : r ≤ ((H.neighborFinset q) ∩ S).card := by
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



theorem in1088_d11_four_shore_has_at_most_two_internal_opposite_vertices
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
    (hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card) :
    ∀ z ∈ C, (W z).card = 4 → (Q z ∩ S).card ≤ 2 := by
  classical
  intro z hz hwcard
  have hinc := in1088_bridge_family_variable_external_incidence_budget H S C 11 4 hSC hS hmax Q W hdis hQ hW
    (by intro a ha; simpa using hsize a ha) hzQ hcross hWmin
  have hwalk := in1088_bridge_family_internal_external_walk_budget H x y hxy S C 11 32 4
    (by omega) (by omega) hSC hxC hyC hS hmax hSxy Q W hdis hQ hW
    (by intro a ha; simpa using hsize a ha) hxQ hyQ hzQ hcross hWmin hprod
  have hdis' : Disjoint (W z) (Q z ∩ S) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp (hdis z hz)) (Finset.mem_inter.mp hb).1 ha
  have hcharge := in1088_complete_bipartite_internal_walk_charge H S (W z) (Q z ∩ S)
    (hW z hz) Finset.inter_subset_right hdis' hwcard
    (by intro a ha b hb; exact (hcross z hz b (Finset.mem_inter.mp hb).1 a ha).symm)
  simp only [Nat.reduceSub, Nat.reduceMul] at hinc hwalk
  have hT : 6 ≤ (C.filter (fun q => 4 ≤ (H.neighborFinset q ∩ S).card)).card := by omega
  by_contra hp
  have hp3 : 3 ≤ (Q z ∩ S).card := by omega
  have hp2 : 2 ≤ (Q z ∩ S).card-1 := by omega
  have hprod' := Nat.mul_le_mul hp3 hp2
  simp only [Nat.mul_assoc] at hcharge
  omega




theorem in1088_four_shore_crossing_intersection_at_least_three
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B W Q : Finset V)
    (hA : A ⊆ S) (hAcard : A.card = 4) (hBcard : B.card = 8)
    (hWQsize : W.card + Q.card = 12)
    (hcrossing : (A ∪ W).card + (B ∩ Q).card = 12)
    (hAW : (A ∩ W).Nonempty) (hxB : x ∉ B) (hyB : y ∉ B)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : 3 ≤ (A ∩ W).card := by
  classical
  obtain ⟨a,ha⟩ := hAW
  have haA : a ∈ A := (Finset.mem_inter.mp ha).1
  have haW : a ∈ W := (Finset.mem_inter.mp ha).2
  let D := Q \ B
  have hd : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro z hz hzD
    exact (Finset.mem_sdiff.mp hzD).2 hz
  have hxD : x ∉ D := by simp [D,hxQ]
  have hyD : y ∉ D := by simp [D,hyQ]
  have hxBD : x ∉ B ∪ D := by simp [hxB,hxD]
  have hyBD : y ∉ B ∪ D := by simp [hyB,hyD]
  have hxnot : x ∉ insert y (B ∪ D) := by simp [hxy,hxBD]
  have hsub : insert x (insert y (B ∪ D)) ⊆ H.neighborFinset a := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_union] at hz
    rcases hz with rfl | rfl | hz | hz
    · simpa using (hSxy a (hA haA)).1
    · simpa using (hSxy a (hA haA)).2
    · simpa using (hBA z hz a haA).symm
    · have hzQ := (Finset.mem_sdiff.mp hz).1
      simpa using (hQW z hzQ a haW).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyBD,
    Finset.card_union_of_disjoint hd,hBcard] at hc
  have hm := hmax a
  have hD : D.card ≤ 1 := by omega
  have hAWsum := Finset.card_union_add_card_inter A W
  have hQBsum := Finset.card_sdiff_add_card_inter Q B
  rw [Finset.inter_comm Q B] at hQBsum
  dsimp [D] at hD
  omega


theorem in1088_four_shore_even_crossing_is_contained
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B W Q : Finset V)
    (hA : A ⊆ S) (hAcard : A.card = 4) (hBcard : B.card = 8)
    (hWQsize : W.card + Q.card = 12)
    (hcrossing : (A ∪ W).card + (B ∩ Q).card = 12)
    (hAW : (A ∩ W).Nonempty) (hAWeven : Even (A ∩ W).card)
    (hxB : x ∉ B) (hyB : y ∉ B) (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : A ⊆ W := by
  classical
  have hl := in1088_four_shore_crossing_intersection_at_least_three H x y hxy S A B W Q
    hA hAcard hBcard hWQsize hcrossing hAW hxB hyB hxQ hyQ hmax hSxy hBA hQW
  have hu : (A ∩ W).card ≤ 4 := by
    have hc := Finset.card_le_card (Finset.inter_subset_left : A ∩ W ⊆ A)
    omega
  obtain ⟨t,ht⟩ := hAWeven
  have hc : (A ∩ W).card = A.card := by omega
  have heq : A ∩ W = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  intro a ha
  have ha' : a ∈ A ∩ W := heq.symm ▸ ha
  exact (Finset.mem_inter.mp ha').2


theorem in1088_bridge_family_no_full_shore {V : Type*} [Fintype V] [DecidableEq V]
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
  have htwo := in1088_bridge_opposite_shore_two_external S C Q W d hSC hQW hQ hW hS hsize
  have hne : (Q ∩ C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := hne
  have hqQ : q ∈ Q := (Finset.mem_inter.mp hq).1
  have hqC : q ∈ C := (Finset.mem_inter.mp hq).2
  obtain ⟨Q',W',hQW',hQ',hW',hsize',hqQ',hcross'⟩ := hfamily q hqC
  have htwo' := in1088_bridge_opposite_shore_two_external S C Q' W' d hSC hQW' hQ' hW' hS hsize'
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



theorem in1088_d11_factorcritical_crossing_bridge_family_has_no_four_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : C.card = 20) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card = 10)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card) (hWeven : ∀ z ∈ C, Even (W z).card)
    (hcutrule : ∀ z ∈ C, ∀ z' ∈ C, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card) :
    ∀ z ∈ C, (W z).card ≠ 4 := by
  classical
  intro z₀ hz₀ hw4
  let A := W z₀
  let B := Q z₀
  have hA : A ⊆ S := hW z₀ hz₀
  have hAcard : A.card=4 := hw4
  have hB : B ⊆ S ∪ C := hQ z₀ hz₀
  have hBcard : B.card=8 := by have hs := hsize z₀ hz₀; dsimp [A,B] at *; omega
  have hxB : x ∉ B := hxQ z₀ hz₀
  have hyB : y ∉ B := hyQ z₀ hz₀
  have hfamily : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=11+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := by
    intro z hz
    exact ⟨Q z,W z,hdis z hz,hQ z hz,hW z hz,by simpa using hsize z hz,hzQ z hz,hcross z hz⟩
  have hW8 : ∀ z ∈ C, (W z).card ≤ 8 := by
    intro z hz
    have hne := in1088_bridge_family_no_full_shore H S C 11 hSC (by omega) hmax hfamily
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (by simpa using hsize z hz)
      (hzQ z hz) (hcross z hz)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hW z hz,hne⟩)
    obtain ⟨m,hm⟩ := hWeven z hz
    omega
  have hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card := by
    intro z hz
    have hw := hW8 z hz
    have hs := hsize z hz
    omega
  have hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card := by
    intro z hz
    have hw4 := hWmin z hz
    have hw8 := hW8 z hz
    have hs := hsize z hz
    obtain ⟨m,hm⟩ := hWeven z hz
    have hwcase : (W z).card=4 ∨ (W z).card=6 ∨ (W z).card=8 := by omega
    rcases hwcase with hw | hw | hw <;> rw [hw] <;> omega
  have hBS : (B ∩ S).card ≤ 2 := by
    have hb := in1088_d11_four_shore_has_at_most_two_internal_opposite_vertices H x y hxy S C
      (by omega) hSC hxC hyC (by omega) hmax hSxy Q W hdis hQ hW hxQ hyQ hsize hzQ hcross hWmin hprod
      z₀ hz₀ hw4
    exact hb
  have hE : 6 ≤ (B ∩ C).card := by
    have hd : Disjoint (B ∩ S) (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (B ∩ S) ∪ (B ∩ C) = B := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB ha) with haS | haC
        · exact Or.inl ⟨ha,haS⟩
        · exact Or.inr ⟨ha,haC⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    omega
  have havoid : ∀ z ∈ C, Disjoint A (Q z) := by
    intro z hz
    exact in1088_four_shore_forces_other_opposite_avoids_shore H x y hxy S A B (Q z) (W z)
      hA (hW z hz) hBcard (hWmin z hz) hBS hxB hyB hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
  have hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B := by
    intro z hz hAW
    have hc := hcutrule z₀ hz₀ z hz hAW
    obtain ⟨heq,heven⟩ := hc
    have hAWsub := in1088_four_shore_even_crossing_is_contained H x y hxy S A B (W z) (Q z)
      hA hAcard hBcard (by have hs := hsize z hz; omega) heq hAW heven hxB hyB (hxQ z hz) (hyQ z hz)
      hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
    refine ⟨hAWsub,?_⟩
    have huni : A ∪ W z = W z := Finset.union_eq_right.mpr hAWsub
    rw [huni] at heq
    change (W z).card + (B ∩ Q z).card = 12 at heq
    have hcard : (B ∩ Q z).card = (Q z).card := by have hs := hsize z hz; omega
    have hset : B ∩ Q z = Q z := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    intro q hq
    exact (Finset.mem_inter.mp (hset.symm ▸ hq)).1
  exact in1088_d11_nested_first_four_shore_impossible H x y z₀ hxy S C A B Q W
    hSC hxC hyC hS hA hAcard hB hBcard hBS hE hz₀ rfl rfl hxB hyB hmax hSxy hQ hW hdis hsize hQ4 hWmin
    hWeven (by intro z hz; exact hW8 z (Finset.mem_inter.mp hz).2) havoid hzQ hcross hnest






theorem in1088_factorcritical_separator_lower_bound
    (k d : ℕ) (G : SimpleGraph (Fin (2*k+d+3)))
    (hcrit : is_k_factor_critical G (2*k))
    (C A B : Finset (Fin (2*k+d+3)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hCA : Disjoint C A) (hCB : Disjoint C B)
    (hAB : Disjoint A B) (hpart : C ∪ A ∪ B = Finset.univ)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : 2*k ≤ C.card := by
  classical
  by_contra hn
  have hCsmall : C.card < 2*k := by omega
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  have hab : a ≠ b := by
    intro heq
    subst b
    exact (Finset.disjoint_left.mp hAB) ha hb
  have haC : a ∉ C := fun h => (Finset.disjoint_left.mp hCA) h ha
  have hbC : b ∉ C := fun h => (Finset.disjoint_left.mp hCB) h hb
  let P : Finset (Fin (2*k+d+3)) := ((Finset.univ \ C).erase a).erase b
  have hPcard : d+2 ≤ P.card := by
    have hC := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    simp only [Finset.card_univ,Fintype.card_fin] at hC
    have haU : a ∈ Finset.univ \ C := by simp [haC]
    have hbU : b ∈ (Finset.univ \ C).erase a := by simp [hbC,hab.symm]
    dsimp [P]
    rw [Finset.card_erase_of_mem hbU,Finset.card_erase_of_mem haU]
    omega
  obtain ⟨T,hTP,hTcard⟩ := Finset.exists_subset_card_eq hPcard
  let S := insert a (insert b T)
  have haT : a ∉ T := by
    intro h
    have := hTP h
    simp [P] at this
  have hbT : b ∉ T := by
    intro h
    have := hTP h
    simp [P] at this
  have hSsize : S.card + 2*k = Fintype.card (Fin (2*k+d+3)) + 1 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem (by simp [hab,haT]),Finset.card_insert_of_notMem hbT,hTcard]
    simp only [Fintype.card_fin]
    omega
  have hSA : a ∈ S := by simp [S]
  have hSB : b ∈ S := by simp [S]
  have hSnotC : ∀ v ∈ S, v ∉ C := by
    intro v hv
    dsimp [S] at hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact haC
    · exact hbC
    · have hvP := hTP hv
      dsimp [P] at hvP
      exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvP))).2
  have hSAB : ∀ v ∈ S, v ∈ A ∨ v ∈ B := by
    intro v hv
    have hp : v ∈ C ∪ A ∪ B := by rw [hpart]; exact Finset.mem_univ v
    rcases Finset.mem_union.mp hp with hp | hb'
    · rcases Finset.mem_union.mp hp with hc | ha'
      · exact ((hSnotC v hv) hc).elim
      · exact Or.inl ha'
    · exact Or.inr hb'
  let D := G.induce {v | v ∈ S}
  have hDcrit : is_k_factor_critical D 1 := factorcritical_induce_one_after_vertex_restriction G (2*k) hcrit S hSsize
  let av : {v // v ∈ S} := ⟨a,hSA⟩
  let bv : {v // v ∈ S} := ⟨b,hSB⟩
  have hne : av ≠ bv := fun he => hab (congrArg Subtype.val he)
  have hconn := nontrivial_factorcritical_graph_connected D hDcrit av bv hne
  have hreach : D.Reachable av bv := hconn.preconnected av bv
  have hprop : ∀ u v : {v // v ∈ S}, D.Reachable u v → u.val ∈ A → v.val ∈ A := by
    intro u v hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => intro hu; exact hu
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      rcases hSAB v.val v.property with hvA | hvB
      · exact hvA
      · exact (hcross u.val hu v.val hvB huv).elim
  have hbA := hprop av bv hreach ha
  exact (Finset.disjoint_left.mp hAB) hbA hb




theorem in1088_factorcritical_crossing_shore_intersection_even
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k d : ℕ) (hcrit : is_k_factor_critical G (2*k))
    (W₁ W₂ Q₁ Q₂ : Finset V) (z₁ z₂ : V)
    (hsize₁ : W₁.card+Q₁.card=d+1) (hsize₂ : W₂.card+Q₂.card=d+1)
    (hW₁even : Even W₁.card) (hW₂even : Even W₂.card) (hQ₁even : Even Q₁.card)
    (heq : (W₁ ∪ W₂).card + (Q₁ ∩ Q₂).card = d+1)
    (hcut : ((Finset.univ : Finset V) \ ((Q₁ ∩ Q₂) ∪ ((W₁ ∪ W₂) ∪ {z₁,z₂}))).card = 2*k)
    (hdisj : Disjoint (Q₁ ∩ Q₂) (W₁ ∪ W₂))
    (hz₁ : z₁ ∉ Q₁ ∩ Q₂) (hz₂ : z₂ ∉ Q₁ ∩ Q₂)
    (hcross₁ : ∀ w ∈ W₁, ∀ q ∈ Q₁, ¬ G.Adj w q)
    (hcross₂ : ∀ w ∈ W₂, ∀ q ∈ Q₂, ¬ G.Adj w q)
    (hend : ∀ q ∈ Q₁ ∩ Q₂, ¬ G.Adj q z₁ ∧ ¬ G.Adj q z₂) :
    Even (W₁ ∩ W₂).card := by
  classical
  have hd : Disjoint (Q₁ ∩ Q₂) ((W₁ ∪ W₂) ∪ {z₁,z₂}) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.disjoint_left.mp hdisj) ha hb
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact hz₁ ha
      · exact hz₂ ha
  have hc : ∀ q ∈ Q₁ ∩ Q₂, ∀ w ∈ (W₁ ∪ W₂) ∪ {z₁,z₂}, ¬ G.Adj q w := by
    intro q hq w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases Finset.mem_union.mp hw with hw | hw
      · intro hadj
        exact hcross₁ w hw q (Finset.mem_inter.mp hq).1 hadj.symm
      · intro hadj
        exact hcross₂ w hw q (Finset.mem_inter.mp hq).2 hadj.symm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (hend q hq).1
      · exact (hend q hq).2
  have hj := factor_critical_anticomplete_cut_side_even G (2*k) hcrit
    (Q₁ ∩ Q₂) ((W₁ ∪ W₂) ∪ {z₁,z₂}) hd hc hcut
  have hu := Finset.card_union_add_card_inter W₁ W₂
  obtain ⟨a,ha⟩ := hW₁even
  obtain ⟨b,hb⟩ := hW₂even
  obtain ⟨c,hc'⟩ := hQ₁even
  obtain ⟨e,he⟩ := hj
  refine ⟨b+e-c,?_⟩
  omega


theorem in1088_factorcritical_bridge_family_crossing_rule
    (k : ℕ) (H : SimpleGraph (Fin (2*k+11+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k))
    (x y : Fin (2*k+11+3)) (hxy : x ≠ y)
    (S C : Finset (Fin (2*k+11+3))) (hS : S.card=10) (hSC : Disjoint S C)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : Fin (2*k+11+3) → Finset (Fin (2*k+11+3)))
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hW : ∀ z ∈ C, W z ⊆ S) (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hWeven : ∀ z ∈ C, Even (W z).card)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w) :
    ∀ z ∈ C, ∀ z' ∈ C, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card := by
  classical
  intro z hz z' hz' hWi
  by_cases hzz : z=z'
  · subst z'
    simp only [Finset.inter_self,Finset.union_self]
    constructor
    · have hs := hsize z hz
      omega
    · exact hWeven z hz
  · have hsep : ∀ C' A B : Finset (Fin (2*k+11+3)),
        A.Nonempty → B.Nonempty → Disjoint C' A → Disjoint C' B → Disjoint A B →
        C' ∪ A ∪ B = Finset.univ →
        (∀ a ∈ A, ∀ b ∈ B, ¬ Hᶜ.Adj a b) → 2*k ≤ C'.card :=
      in1088_factorcritical_separator_lower_bound k 11 Hᶜ hcrit
    have hxS : x ∉ S := by intro h; exact (hSxy x h).1.ne rfl
    have hyS : y ∉ S := by intro h; exact (hSxy y h).2.ne rfl
    have hxW : x ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hxS (hW z hz h)
      · exact hxS (hW z' hz' h)
    have hyW : y ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hyS (hW z hz h)
      · exact hyS (hW z' hz' h)
    have hxQ' : x ∉ Q z ∪ Q z' := by simp [hxQ z hz,hxQ z' hz']
    have hyQ' : y ∉ Q z ∪ Q z' := by simp [hyQ z hz,hyQ z' hz']
    have hzW : z ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.disjoint_left.mp hSC) (hW z hz h) hz
      · exact (Finset.disjoint_left.mp hSC) (hW z' hz' h) hz
    have hz'W : z' ∉ W z ∪ W z' := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.disjoint_left.mp hSC) (hW z hz h) hz'
      · exact (Finset.disjoint_left.mp hSC) (hW z' hz' h) hz'
    have hzQi : z ∉ Q z ∩ Q z' := by
      intro h
      exact (hzQ z hz z (Finset.mem_inter.mp h).1).ne rfl
    have hz'Qi : z' ∉ Q z ∩ Q z' := by
      intro h
      exact (hzQ z' hz' z' (Finset.mem_inter.mp h).2).ne rfl
    have hdisj₁ : Disjoint (W z ∩ W z') (Q z ∪ Q z') := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.disjoint_left.mp (hdis z hz)) hb (Finset.mem_inter.mp ha).1
      · exact (Finset.disjoint_left.mp (hdis z' hz')) hb (Finset.mem_inter.mp ha).2
    have hdisj₂ : Disjoint (Q z ∩ Q z') (W z ∪ W z') := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.disjoint_left.mp (hdis z hz)) (Finset.mem_inter.mp ha).1 hb
      · exact (Finset.disjoint_left.mp (hdis z' hz')) (Finset.mem_inter.mp ha).2 hb
    have hcross₁ : ∀ w ∈ W z, ∀ q ∈ Q z, ¬ Hᶜ.Adj w q := by
      intro w hw q hq hadj
      exact hadj.2 (hcross z hz q hq w hw).symm
    have hcross₂ : ∀ w ∈ W z', ∀ q ∈ Q z', ¬ Hᶜ.Adj w q := by
      intro w hw q hq hadj
      exact hadj.2 (hcross z' hz' q hq w hw).symm
    have htwins : ∀ w ∈ W z ∪ W z', ¬ Hᶜ.Adj w x ∧ ¬ Hᶜ.Adj w y := by
      intro w hw
      have hwS : w ∈ S := by
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hW z hz hw
        · exact hW z' hz' hw
      exact ⟨fun ha => ha.2 (hSxy w hwS).1, fun ha => ha.2 (hSxy w hwS).2⟩
    have hend : ∀ q ∈ Q z ∩ Q z', ¬ Hᶜ.Adj q z ∧ ¬ Hᶜ.Adj q z' := by
      intro q hq
      exact ⟨fun ha => ha.2 (hzQ z hz q (Finset.mem_inter.mp hq).1).symm,
        fun ha => ha.2 (hzQ z' hz' q (Finset.mem_inter.mp hq).2).symm⟩
    have hWbound : (W z ∪ W z').card+1 ≤ 11 := by
      have hs : W z ∪ W z' ⊆ S := Finset.union_subset (hW z hz) (hW z' hz')
      have hc := Finset.card_le_card hs
      omega
    have hQi2 := crossing_shores_force_two_common_opposite_vertices k 11 Hᶜ (W z) (W z') (Q z) (Q z') x y
      hsep hWi (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      hWbound hxy hxW hyW hxQ' hyQ' hdisj₁ hcross₁ hcross₂ htwins
    have hQi : (Q z ∩ Q z').Nonempty := Finset.card_pos.mp (by omega)
    have hcut := crossing_bridge_shores_force_cut_equality k 11 Hᶜ (W z) (W z') (Q z) (Q z') x y z z'
      hsep hWi hQi (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      hxy hzz hxW hyW hxQ' hyQ' hzW hz'W hzQi hz'Qi hdisj₁ hdisj₂ hcross₁ hcross₂ htwins hend
    have hQeven : Even (Q z).card := by
      obtain ⟨m,hm⟩ := hWeven z hz
      have hs := hsize z hz
      refine ⟨6-m,?_⟩
      omega
    have heven := in1088_factorcritical_crossing_shore_intersection_even Hᶜ k 11 hcrit (W z) (W z') (Q z) (Q z') z z'
      (by have hs := hsize z hz; omega) (by have hs := hsize z' hz'; omega)
      (hWeven z hz) (hWeven z' hz') hQeven (by have := hcut.1; omega)
      (by simpa only [Finset.union_assoc] using hcut.2.2) hdisj₂ hzQi hz'Qi hcross₁ hcross₂ hend
    exact ⟨by have := hcut.1; omega,heven⟩



theorem in1088_d11_factorcritical_crossing_large_bridge_family_has_no_four_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : 20 ≤ C.card) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card = 10)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card) (hWeven : ∀ z ∈ C, Even (W z).card)
    (hcutrule : ∀ z ∈ C, ∀ z' ∈ C, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card) :
    ∀ z ∈ C, (W z).card ≠ 4 := by
  classical
  intro z₀ hz₀ hw4
  let A := W z₀
  let B := Q z₀
  have hA : A ⊆ S := hW z₀ hz₀
  have hAcard : A.card=4 := hw4
  have hB : B ⊆ S ∪ C := hQ z₀ hz₀
  have hBcard : B.card=8 := by have hs := hsize z₀ hz₀; dsimp [A,B] at *; omega
  have hxB : x ∉ B := hxQ z₀ hz₀
  have hyB : y ∉ B := hyQ z₀ hz₀
  have hfamily : ∀ z ∈ C, ∃ Q' W' : Finset V, Disjoint Q' W' ∧ Q' ⊆ S ∪ C ∧ W' ⊆ S ∧
      Q'.card+W'.card=11+1 ∧ (∀ q ∈ Q', H.Adj z q) ∧
      (∀ q ∈ Q', ∀ w ∈ W', H.Adj q w) := by
    intro z hz
    exact ⟨Q z,W z,hdis z hz,hQ z hz,hW z hz,by simpa using hsize z hz,hzQ z hz,hcross z hz⟩
  have hW8 : ∀ z ∈ C, (W z).card ≤ 8 := by
    intro z hz
    have hne := in1088_bridge_family_no_full_shore H S C 11 hSC (by omega) hmax hfamily
      z hz (Q z) (W z) (hdis z hz) (hQ z hz) (hW z hz) (by simpa using hsize z hz)
      (hzQ z hz) (hcross z hz)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hW z hz,hne⟩)
    obtain ⟨m,hm⟩ := hWeven z hz
    omega
  have hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card := by
    intro z hz
    have hw := hW8 z hz
    have hs := hsize z hz
    omega
  have hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card := by
    intro z hz
    have hw4 := hWmin z hz
    have hw8 := hW8 z hz
    have hs := hsize z hz
    obtain ⟨m,hm⟩ := hWeven z hz
    have hwcase : (W z).card=4 ∨ (W z).card=6 ∨ (W z).card=8 := by omega
    rcases hwcase with hw | hw | hw <;> rw [hw] <;> omega
  have hBS : (B ∩ S).card ≤ 2 := by
    have hb := in1088_d11_four_shore_has_at_most_two_internal_opposite_vertices H x y hxy S C
      (by omega) hSC hxC hyC (by omega) hmax hSxy Q W hdis hQ hW hxQ hyQ hsize hzQ hcross hWmin hprod
      z₀ hz₀ hw4
    exact hb
  have hE : 6 ≤ (B ∩ C).card := by
    have hd : Disjoint (B ∩ S) (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (B ∩ S) ∪ (B ∩ C) = B := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB ha) with haS | haC
        · exact Or.inl ⟨ha,haS⟩
        · exact Or.inr ⟨ha,haC⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    omega
  have havoid : ∀ z ∈ C, Disjoint A (Q z) := by
    intro z hz
    exact in1088_four_shore_forces_other_opposite_avoids_shore H x y hxy S A B (Q z) (W z)
      hA (hW z hz) hBcard (hWmin z hz) hBS hxB hyB hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
  have hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B := by
    intro z hz hAW
    have hc := hcutrule z₀ hz₀ z hz hAW
    obtain ⟨heq,heven⟩ := hc
    have hAWsub := in1088_four_shore_even_crossing_is_contained H x y hxy S A B (W z) (Q z)
      hA hAcard hBcard (by have hs := hsize z hz; omega) heq hAW heven hxB hyB (hxQ z hz) (hyQ z hz)
      hmax hSxy
      (by intro b hb a ha; exact hcross z₀ hz₀ b hb a ha)
      (hcross z hz)
    refine ⟨hAWsub,?_⟩
    have huni : A ∪ W z = W z := Finset.union_eq_right.mpr hAWsub
    rw [huni] at heq
    change (W z).card + (B ∩ Q z).card = 12 at heq
    have hcard : (B ∩ Q z).card = (Q z).card := by have hs := hsize z hz; omega
    have hset : B ∩ Q z = Q z := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    intro q hq
    exact (Finset.mem_inter.mp (hset.symm ▸ hq)).1
  exact in1088_d11_nested_first_four_shore_impossible H x y z₀ hxy S C A B Q W
    hSC hxC hyC hS hA hAcard hB hBcard hBS hE hz₀ rfl rfl hxB hyB hmax hSxy hQ hW hdis hsize hQ4 hWmin
    hWeven (by intro z hz; exact hW8 z (Finset.mem_inter.mp hz).2) havoid hzQ hcross hnest

theorem factorcritical_minimal_d11_kge9_excludes_saturated_twins
    (k : ℕ) (hk : 9 ≤ k) (H : SimpleGraph (Fin (2*k+11+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (hmin : is_minimally_k_extendable Hᶜ k)
    (x y : Fin (2*k+11+3)) (hxy : H.Adj x y)
    (hxdeg : (H.neighborFinset x).card = 11) (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) : False := by
  classical
  let S := (H.neighborFinset x).erase y
  let C := (Hᶜ).neighborFinset x
  have hxS : x ∉ S := by simp [S]
  have hyS : y ∉ S := by simp [S]
  have hxC : x ∉ C := by simp [C]
  have hyC : y ∉ C := by simp [C,hxy]
  have hSC : Disjoint S C := by
    apply Finset.disjoint_left.mpr
    intro a haS haC
    have haG : (Hᶜ).Adj x a := by simpa [C] using haC
    have haH : H.Adj x a := by
      have := Finset.mem_of_mem_erase haS
      simpa using this
    exact haG.2 haH
  have hyN : y ∈ H.neighborFinset x := by simpa using hxy
  have hSsize : S.card+1=11 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hyN,hxdeg]
  have hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y := by
    intro a haS
    have hay : a ≠ y := Finset.ne_of_mem_erase haS
    have hxa : H.Adj x a := by
      have haN := Finset.mem_of_mem_erase haS
      simpa using haN
    have hax : a ≠ x := hxa.ne.symm
    exact ⟨hxa.symm, ((htwin a hax hay).mp hxa).symm⟩
  have hxyG := complement_adjacent_twins_have_equal_open_neighbors H x y hxy htwin
  have hmaxG : ∀ a, (((Hᶜ)ᶜ).neighborFinset a).card ≤ 11 := by
    intro a
    have hN : (((Hᶜ)ᶜ).neighborFinset a) = H.neighborFinset a := by ext b; simp
    rw [hN]
    exact hmax a
  have hfamily : ∀ z ∈ C, ∃ Q W : Finset (Fin (2*k+11+3)),
      Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧ x ∉ Q ∧ y ∉ Q ∧
      Q.card+W.card=11+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ 2 ≤ W.card ∧ Even Q.card ∧ Even W.card := by
    intro z hzC
    have hxzG : (Hᶜ).Adj x z := by simpa [C] using hzC
    have he : s(x,z) ∈ (Hᶜ).edgeSet := by simpa using hxzG
    have hessential := hmin.2 s(x,z) he
    obtain ⟨R,hR,hxR,hzR,hPM,hf⟩ := k_extendable_essential_edge_has_forced_matching_residual
      (2*k+11+3) k Hᶜ x z hxzG hmin.1 hessential
    have hR' : R.card=11+3 := by omega
    obtain ⟨hyR,Q,W,hdis,hpartR,hxQ,hzQ,hxW,hzW,hyQ,hyW,hqmin,hwmin,hqe,hwe,hsum,hzQ,hxyW,hcross⟩ :=
      factorcritical_false_twin_forced_bridge_residual_shores Hᶜ k hcrit rfl x y z hxy.ne hxyG hxzG hmaxG R hR' hxR hzR hPM hf
    have hQsub : Q ⊆ S ∪ C := by
      intro q hq
      have hqx : q ≠ x := fun h => hxQ (h ▸ hq)
      have hqy : q ≠ y := fun h => hyQ (h ▸ hq)
      by_cases h : H.Adj x q
      · apply Finset.mem_union_left
        exact Finset.mem_erase.mpr ⟨hqy, by simpa using h⟩
      · apply Finset.mem_union_right
        have hG : (Hᶜ).Adj x q := ⟨hqx.symm,h⟩
        simpa [C] using hG
    have hWsub : W ⊆ S := by
      intro w hw
      have hwH : H.Adj x w := by simpa using (hxyW w hw).1
      have hwy : w ≠ y := fun h => hyW (h ▸ hw)
      exact Finset.mem_erase.mpr ⟨hwy, by simpa using hwH⟩
    refine ⟨Q,W,hdis,hQsub,hWsub,hxQ,hyQ,hsum,?_,?_,hwmin,hqe,hwe⟩
    · intro q hq
      simpa using hzQ q hq
    · intro q hq w hw
      simpa using hcross q hq w hw
  have hfull : ∀ z, ∃ Q W : Finset (Fin (2*k+11+3)), z ∈ C →
      Disjoint Q W ∧ Q ⊆ S ∪ C ∧ W ⊆ S ∧ x ∉ Q ∧ y ∉ Q ∧
      Q.card+W.card=11+1 ∧ (∀ q ∈ Q, H.Adj z q) ∧
      (∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) ∧ 2 ≤ W.card ∧ Even Q.card ∧ Even W.card := by
    intro z
    by_cases hz : z ∈ C
    · obtain ⟨Q,W,h⟩ := hfamily z hz
      exact ⟨Q,W,fun _ => h⟩
    · exact ⟨∅,∅,fun h => (hz h).elim⟩
  choose Q W hp using hfull
  have hCcard : C.card = 2*k+2 := by
    dsimp [C]
    change (Hᶜ).degree x = 2*k+2
    have hdeg : H.degree x = 11 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hxdeg
    have hc := H.degree_compl (v := x)
    simp only [Fintype.card_fin] at hc
    rw [hdeg] at hc
    omega
  have hd : ∀ z ∈ C, Disjoint (Q z) (W z) := by
    intro z hz
    obtain ⟨a,_,_,_,_,_,_,_,_,_,_⟩ := hp z hz
    exact a
  have hq : ∀ z ∈ C, Q z ⊆ S ∪ C := by
    intro z hz
    obtain ⟨_,a,_,_,_,_,_,_,_,_,_⟩ := hp z hz
    exact a
  have hw : ∀ z ∈ C, W z ⊆ S := by
    intro z hz
    obtain ⟨_,_,a,_,_,_,_,_,_,_,_⟩ := hp z hz
    exact a
  have hqx : ∀ z ∈ C, x ∉ Q z := by
    intro z hz
    obtain ⟨_,_,_,a,_,_,_,_,_,_,_⟩ := hp z hz
    exact a
  have hqy : ∀ z ∈ C, y ∉ Q z := by
    intro z hz
    obtain ⟨_,_,_,_,a,_,_,_,_,_,_⟩ := hp z hz
    exact a
  have hs : ∀ z ∈ C, (Q z).card+(W z).card=12 := by
    intro z hz
    obtain ⟨_,_,_,_,_,a,_,_,_,_,_⟩ := hp z hz
    omega
  have hzq : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,a,_,_,_,_⟩ := hp z hz
    exact a
  have hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,_,a,_,_,_⟩ := hp z hz
    exact a
  have hw2 : ∀ z ∈ C, 2 ≤ (W z).card := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,_,_,a,_,_⟩ := hp z hz
    exact a
  have hwe : ∀ z ∈ C, Even (W z).card := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,_,_,_,_,a⟩ := hp z hz
    exact a
  have hw4 : ∀ z ∈ C, 4 ≤ (W z).card := by
    intro z hz
    have hWne : (W z).Nonempty := Finset.card_pos.mp (by have := hw2 z hz; omega)
    obtain ⟨w,hwm⟩ := hWne
    have hx : H.Adj w x := (hSxy w (hw z hz hwm)).1
    have hy : H.Adj w y := (hSxy w (hw z hz hwm)).2
    have hsub : insert x (insert y (Q z)) ⊆ H.neighborFinset w := by
      intro a ha
      rw [H.mem_neighborFinset]
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact hx
      · exact hy
      · exact (hcross z hz a ha w hwm).symm
    have hxnot : x ∉ insert y (Q z) := by simp [hxy.ne,hqx z hz]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem (hqy z hz)] at hc
    have hm := hmax w
    obtain ⟨m,hm'⟩ := hwe z hz
    have hsum := hs z hz
    omega
  have hcut := in1088_factorcritical_bridge_family_crossing_rule k H hcrit x y hxy.ne S C
    (by omega) hSC hSxy Q W hd hw hqx hqy hs hwe hzq hcross
  have hno4 := in1088_d11_factorcritical_crossing_large_bridge_family_has_no_four_shore H x y hxy.ne S C
    (by omega) hSC hxC hyC (by omega) hmax hSxy Q W hd hq hw hqx hqy hs hzq hcross hw4 hwe hcut
  have hqe : ∀ z ∈ C, Even (Q z).card := by
    intro z hz
    obtain ⟨_,_,_,_,_,_,_,_,_,a,_⟩ := hp z hz
    exact a
  obtain ⟨z,hz,hw4⟩ := d11_large_bridge_family_forces_four_shore H x y hxy.ne S C
    (by omega) hSC hxC hyC (by omega) hmax hSxy Q W hd hq hw hqx hqy hs hzq hcross hw4 hqe hwe
  exact hno4 z hz hw4
