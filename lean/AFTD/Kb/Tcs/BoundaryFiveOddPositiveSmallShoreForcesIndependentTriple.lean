import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition
import AFTD.Kb.Tcs.SaturatedBarrierGroupsOutsideBAtMostTwo
import AFTD.Kb.Tcs.SaturatedSmallShoreSingletonPoolEmpty
import AFTD.Kb.Tcs.SaturatedPositiveSmallShoreForcesTwoSingletonGroups
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Op1957TwoExceptionalGroupsExactBlockPool
import AFTD.Kb.Tcs.Op1957ExceptionalSlotsFourShoreStructure
import AFTD.Kb.Tcs.Op1957SmallShoreFourGroupNumericAssembly
import AFTD.Kb.Tcs.Op1957TwoExceptionalSlotsForceIndependentTriple
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedTwoOddShoresForcePatterns

/-!
# boundary_five_odd_positive_small_shore_forces_independent_triple

Topic: graphs   Node: a40276329347

Provenance: helper lemma. OP-1957: small-shore positive-barrier assembly with extendibility and an independence bound.

Under the displayed saturated five-by-odd partition, extendibility, independence, degree and separator hypotheses, a positive barrier whose x-shore meets A in at most two vertices forces p, q and y to be pairwise nonadjacent.
-/

set_option maxHeartbeats 3000000
open scoped BigOperators

theorem boundary_five_odd_positive_small_shore_forces_independent_triple
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hext : is_k_extendable G k)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ k)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x p q y : Fin (4*k)) (hxA : x ∈ A) (hp : p ∈ C) (hq : q ∈ C)
    (hpq : p ≠ q) (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hyC : y ∈ C) (hyp : y ≠ p) (hyq : y ≠ q)
    (X Y U : Finset (Fin (4*k))) (s : ℕ)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hxX : x ∈ X) (hyY : y ∈ Y) (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (hs : 1 ≤ s) (hsize : X.card+Y.card+U.card+s=2*k)
    (hUodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hUparity : U.card % 2 = s % 2)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u)
    (hsmall : (X ∩ A).card ≤ 2) :
    ¬ G.Adj p q ∧ ¬ G.Adj y p ∧ ¬ G.Adj y q := by
  classical
  have hxU : x ∉ U := fun hu => Finset.disjoint_left.mp hXU hxX hu
  have hanti : ∀ u ∈ U, ¬ G.Adj x u := fun u hu => hantiX x hxX u hu
  have hregion : Y ∪ U ⊆ B ∪ {p,q,y} :=
    in1159_saturated_other_shores_subset G A B C D X Y U x y p q
      hAC hCD hcover hxX hyC hXY hXU hcross hanti hsatA hsatD hfull
  have hotherBC : Y ∪ U ⊆ B ∪ C := by
    intro z hz
    have hh := hregion hz
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
    rcases hh with hb | rfl | rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hp
    · exact Or.inr hq
    · exact Or.inr hyC
  have hYBC : Y ⊆ B ∪ C := fun z hz => hotherBC (Finset.mem_union_left _ hz)
  have hUBC : U ⊆ B ∪ C := fun z hz => hotherBC (Finset.mem_union_right _ hz)
  obtain ⟨R,hRodd,hRdis,hRcover⟩ := op1957_odd_components_ambient_partition G U s hs hUodd hUparity
  let K : Finset (Fin s) := Finset.univ
  have hsub : ∀ i ∈ K, R i ⊆ U := by intro i _; exact (hRodd i).1
  have hne : ∀ i ∈ K, (R i).Nonempty := by
    intro i _
    apply Finset.card_pos.mp
    obtain ⟨t,ht⟩ := (hRodd i).2
    omega
  have hd : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (R i) (R j) := by
    intro i _ j _ hij
    exact (hRdis i j hij).1
  have hantiR : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j, ¬ G.Adj u v := by
    intro i _ j _ hij
    exact (hRdis i j hij).2
  have hout := saturated_barrier_groups_outside_b_at_most_two G A B C D U x p q
    hcover hxU hanti hsatA hsatD hfull K R hsub hd
  obtain ⟨J,hJK,P,Q,hJB,houtside,hP,hQ,hslot,hPQ,hJdis,hcount,heb⟩ :=
    op1957_two_exceptional_groups_exact_block_pool K R B hne hd hout
  let F : Fin 4 → Finset (Fin (4*k)) := ![X,Y,P,Q]
  let E : Finset (Fin (4*k)) := J.biUnion R
  have hstructure := op1957_exceptional_slots_four_shore_structure G K J R U X Y P Q x y hJK hsub hne hd hantiR
    (by simpa [K] using hRcover) hP hQ hslot hPQ hXY hXU hYU hcross hantiX hantiY
  dsimp only at hstructure
  obtain ⟨hPU,hQU,hEU,hUeq,hFdis,hEdis,hcross4,hEanti⟩ := hstructure
  have hEB : E ⊆ B := by
    intro v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hJB i hi hvi
  have hPB : P ⊆ B ∪ C := fun v hv => hUBC (hPU hv)
  have hQB : Q ⊆ B ∪ C := fun v hv => hUBC (hQU hv)
  have hBCA : Disjoint (B ∪ C) A := Finset.disjoint_union_left.mpr ⟨hAB.symm,hAC.symm⟩
  have hBCD : Disjoint (B ∪ C) D := Finset.disjoint_union_left.mpr ⟨hBD,hCD⟩
  have hFA : ∀ i : Fin 4, i ≠ 0 → Disjoint (F i) A := by
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · simpa [F] using Finset.disjoint_of_subset_left hYBC hBCA
    · simpa [F] using Finset.disjoint_of_subset_left hPB hBCA
    · simpa [F] using Finset.disjoint_of_subset_left hQB hBCA
  have hFD : ∀ i : Fin 4, i ≠ 0 → Disjoint (F i) D := by
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · simpa [F] using Finset.disjoint_of_subset_left hYBC hBCD
    · simpa [F] using Finset.disjoint_of_subset_left hPB hBCD
    · simpa [F] using Finset.disjoint_of_subset_left hQB hBCD
  have hPgood : P.Nonempty → 1 ≤ (P ∩ C).card := by
    intro hpne
    rcases hP with hp0 | ⟨i,hi,hpi⟩
    · simp [hp0] at hpne
    · obtain ⟨v,hv⟩ := houtside i hi
      have hvR := (Finset.mem_sdiff.mp hv).1
      have hvnB := (Finset.mem_sdiff.mp hv).2
      have hvC : v ∈ C := by
        rcases Finset.mem_union.mp (hUBC (hsub i (Finset.mem_sdiff.mp hi).1 hvR)) with hb | hc
        · exact False.elim (hvnB hb)
        · exact hc
      exact Finset.card_pos.mpr ⟨v,Finset.mem_inter.mpr ⟨hpi.symm ▸ hvR,hvC⟩⟩
  have hQgood : Q.Nonempty → 1 ≤ (Q ∩ C).card := by
    intro hqne
    rcases hQ with hq0 | ⟨i,hi,hqi⟩
    · simp [hq0] at hqne
    · obtain ⟨v,hv⟩ := houtside i hi
      have hvR := (Finset.mem_sdiff.mp hv).1
      have hvnB := (Finset.mem_sdiff.mp hv).2
      have hvC : v ∈ C := by
        rcases Finset.mem_union.mp (hUBC (hsub i (Finset.mem_sdiff.mp hi).1 hvR)) with hb | hc
        · exact False.elim (hvnB hb)
        · exact hc
      exact Finset.card_pos.mpr ⟨v,Finset.mem_inter.mpr ⟨hqi.symm ▸ hvR,hvC⟩⟩
  have he2 : ((F 2 ∩ C).card=0 ∧ (F 2 ∩ B).card=0) ∨ 1 ≤ (F 2 ∩ C).card := by
    by_cases hn : P.Nonempty
    · exact Or.inr (by simpa [F] using hPgood hn)
    · have hp0 : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      exact Or.inl (by simp [F,hp0])
  have he3 : ((F 3 ∩ C).card=0 ∧ (F 3 ∩ B).card=0) ∨ 1 ≤ (F 3 ∩ C).card := by
    by_cases hn : Q.Nonempty
    · exact Or.inr (by simpa [F] using hQgood hn)
    · have hq0 : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      exact Or.inl (by simp [F,hq0])
  have hPocc : (if P.Nonempty then 1 else 0) = (if 1 ≤ (P ∩ C).card then 1 else 0) := by
    by_cases hn : P.Nonempty
    · simp [hn,hPgood hn]
    · have hp0 : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hp0]
  have hQocc : (if Q.Nonempty then 1 else 0) = (if 1 ≤ (Q ∩ C).card then 1 else 0) := by
    by_cases hn : Q.Nonempty
    · simp [hn,hQgood hn]
    · have hq0 : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hq0]
  have hUcard : U.card=P.card+Q.card+E.card := by
    rw [hUeq,Finset.card_union_of_disjoint,Finset.card_union_of_disjoint hPQ]
    exact Finset.disjoint_union_left.mpr ⟨hEdis 2,hEdis 3⟩
  have hcount' : J.card+(if 1 ≤ (P ∩ C).card then 1 else 0)+
      (if 1 ≤ (Q ∩ C).card then 1 else 0)=s := by
    simpa [K,hPocc,hQocc] using hcount
  have hsize' : (∑ i : Fin 4, (F i).card)+E.card+J.card+
      (if 1 ≤ (F 2 ∩ C).card then 1 else 0)+
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0)=2*k := by
    simp only [Fin.sum_univ_four]
    change X.card+Y.card+P.card+Q.card+E.card+J.card+
      (if 1 ≤ (P ∩ C).card then 1 else 0)+
      (if 1 ≤ (Q ∩ C).card then 1 else 0)=2*k
    dsimp only [E] at hUcard ⊢
    omega
  have hspos' : 1 ≤ J.card+(if 1 ≤ (F 2 ∩ C).card then 1 else 0)+
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0) := by
    simpa [F,←hcount'] using hs
  have hRodd' : ∀ i ∈ J, Odd (R i).card := fun i _ => (hRodd i).2
  have hRdis' : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (R i) (R j) :=
    fun i hi j hj hij => hd i (hJK hi) j (hJK hj) hij
  have hRanti' : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j, ¬ G.Adj u v :=
    fun i hi j hj hij => hantiR i (hJK hi) j (hJK hj) hij
  have hCpos := op1957_small_shore_four_group_numeric_assembly k c hc hkc G A B C D E F J R x y p q
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hcritB hconnB hext hind hdegree hsep
    hFdis hEdis hEB hFA hFD hxA hyC (by simpa [F] using hxX) (by simpa [F] using hyY)
    hfull hcross4 hEanti hRodd' hRdis' hRanti' rfl (by simpa [F] using hoddX) (by simpa [F] using hoddY)
    (by simpa [F] using hsmall) he2 he3 heb hsize' hspos'
  have hPQanti : ∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b := by
    intro a ha b hb hab
    have hh := hcross4 2 3 (by decide) a (by simpa [F] using ha) b (by simpa [F] using hb) hab
    simp at hh
  exact op1957_two_exceptional_slots_force_independent_triple G C X Y U P Q x y p q hxX hyY hPU hQU hPQ
    (by simpa [F] using hCpos.1) (by simpa [F] using hCpos.2) hfull hantiX hantiY hPQanti
