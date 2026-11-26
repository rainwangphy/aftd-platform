import AFTD.Prelude
import AFTD.Kb.Tcs.FiveOddSaturatedSmallShoreAggregatePatternsNoConnectedness
import AFTD.Kb.Tcs.FiveOddSaturatedLargeShoreAggregatePattern
import AFTD.Kb.Tcs.SaturatedBarrierOtherShoresAvoidOuterBlocks
import AFTD.Kb.Tcs.FiveOddSaturatedSmallShoreArithmeticNoConnectedness
import AFTD.Kb.Tcs.FiveOddSaturatedLargeShoreArithmeticCore
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedIncidenceBudgets
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# boundary_five_odd_saturated_two_odd_shores_force_patterns

Topic: graphs   Node: f06bc147af52

Provenance: helper lemma. OP-1957; bridge-residual subcase of the five-by-odd saturated essential-edge pattern reduction.

Under the displayed five-by-odd block, degree, separator, B-block connectedness and saturation hypotheses, two disjoint odd shores of total size 2k with a unique crossing edge xy force either two common A-block defects at y and one of p,q, all four A vertices besides x to miss y, or the stated common nonneighbor pattern for p,q,y.
-/

set_option maxHeartbeats 2000000

theorem in1159_saturated_other_shores_subset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B C D X Y U : Finset V) (x y p q : V)
    (hAC : Disjoint A C) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hx : x ∈ X) (hy : y ∈ C)
    (hXY : Disjoint X Y) (hXU : Disjoint X U)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ¬ G.Adj x a)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z) :
    Y ∪ U ⊆ B ∪ {p,q,y} := by
  classical
  intro z hz
  have hzx : z ≠ x := by
    intro h
    subst z
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.disjoint_left.mp hXY hx hz
    · exact Finset.disjoint_left.mp hXU hx hz
  have hxf : G.Adj x z → z = y := by
    intro h
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hcross x hx z hz h).2
    · exact False.elim (hanti z hz h)
  have hzpart : z ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
  simp only [Finset.mem_union] at hzpart
  rcases hzpart with ((ha | hb) | hc) | hd
  · have he := hxf (hsatA z ha hzx)
    exact False.elim (Finset.disjoint_left.mp hAC ha (he ▸ hy))
  · exact Finset.mem_union_left _ hb
  · by_cases hp : z=p
    · simp [hp]
    · by_cases hq : z=q
      · simp [hq]
      · have he := hxf (hfull z hc hp hq)
        simp [he]
  · have he := hxf (hsatD z hd)
    exact False.elim (Finset.disjoint_left.mp hCD (he ▸ hy) hd)

theorem in1159_cross_shore_defect_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y T : Finset V) (x y v : V) (hXY : Disjoint X Y) (hv : v ∈ X)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hvT : v ∉ T) (hantiT : ∀ z ∈ T, ¬ G.Adj v z)
    (d r : ℕ) (hsize : Fintype.card V = T.card + d + 1)
    (hdegree : d ≤ (G.neighborFinset v).card + r) :
    ((Y.erase y) \ T).card ≤ r ∧ (v ≠ x → (Y \ T).card ≤ r) := by
  classical
  have hb := anticomplete_neighbor_defect_bound G T v hvT hantiT d r hsize hdegree
  have hvY : v ∉ Y := fun hh => Finset.disjoint_left.mp hXY hv hh
  constructor
  · apply le_trans (Finset.card_le_card ?_) hb
    intro w hw
    obtain ⟨hwY,hwT⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwy,hwY⟩ := Finset.mem_erase.mp hwY
    have hwv : w ≠ v := fun h => hvY (h ▸ hwY)
    have hnon : ¬ G.Adj v w := fun h => hwy (hcross v hv w hwY h).2
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hwv,hwT⟩,hnon⟩
  · intro hvx
    apply le_trans (Finset.card_le_card ?_) hb
    intro w hw
    obtain ⟨hwY,hwT⟩ := Finset.mem_sdiff.mp hw
    have hwv : w ≠ v := fun h => hvY (h ▸ hwY)
    have hnon : ¬ G.Adj v w := fun h => hvx (hcross v hv w hwY h).1
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hwv,hwT⟩,hnon⟩

theorem in1159_large_shore_two_common_defects
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A C X Y : Finset V) (x y p q : V)
    (hxA : x ∈ A) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (hA : 3 ≤ (A ∩ X).card) (hC : 2 ≤ (C ∩ Y).card) :
    ∃ r ∈ ({p,q} : Finset V), ∃ W ⊆ A.erase x, W.card=2 ∧
      ∀ a ∈ W, ¬ G.Adj a y ∧ ¬ G.Adj a r := by
  classical
  have hr : ∃ r ∈ ({p,q} : Finset V), r ∈ Y := by
    by_cases hp : p ∈ Y
    · exact ⟨p,by simp,hp⟩
    · by_cases hq : q ∈ Y
      · exact ⟨q,by simp,hq⟩
      · have hsub : C ∩ Y ⊆ {y} := by
          intro z hz
          have hzC := (Finset.mem_inter.mp hz).1
          have hzY := (Finset.mem_inter.mp hz).2
          have hzp : z ≠ p := by intro h; exact hp (h ▸ hzY)
          have hzq : z ≠ q := by intro h; exact hq (h ▸ hzY)
          have hzy := (hcross x hxX z hzY (hfull z hzC hzp hzq)).2
          simpa using hzy
        have hh := Finset.card_le_card hsub
        simp at hh
        omega
  obtain ⟨r,hr,hrY⟩ := hr
  have hxAX : x ∈ A ∩ X := Finset.mem_inter.mpr ⟨hxA,hxX⟩
  have hbig : 2 ≤ ((A ∩ X).erase x).card := by
    rw [Finset.card_erase_of_mem hxAX]
    omega
  obtain ⟨W,hWsub,hWcard⟩ := Finset.exists_subset_card_eq hbig
  refine ⟨r,hr,W,?_,hWcard,?_⟩
  · intro a ha
    have ha' := Finset.mem_erase.mp (hWsub ha)
    exact Finset.mem_erase.mpr ⟨ha'.1,(Finset.mem_inter.mp ha'.2).1⟩
  · intro a ha
    have ha' := Finset.mem_erase.mp (hWsub ha)
    have haX := (Finset.mem_inter.mp ha'.2).2
    constructor
    · intro h
      exact ha'.1 (hcross a haX y hyY h).1
    · intro h
      exact ha'.1 (hcross a haX r hrY h).1

theorem in1159_tight_defect_budget_forces_two_edges
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B C U Z : Finset V) (p q y : V) (c : ℕ)
    (hc : 4 ≤ c) (hqC : q ∈ C) (hyC : y ∈ C)
    (hqp : q ≠ p) (hyp : y ≠ p) (hpZ : p ∉ Z) (hqZ : q ∉ Z) (hyZ : y ∉ Z)
    (hUB : U ⊆ B) (hZC : Z ⊆ C)
    (hU : ∀ b ∈ U, ¬ G.Adj b p) (hZ : ∀ z ∈ Z, ¬ G.Adj z p)
    (hsize : U.card + Z.card = c-4)
    (hbudget : (B.filter (fun b => ¬ G.Adj b p)).card +
      ((C.erase p).filter (fun z => ¬ G.Adj p z)).card + 1 ≤ c-3) :
    G.Adj p q ∧ G.Adj y p := by
  classical
  have hUsub : U ⊆ B.filter (fun b => ¬ G.Adj b p) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨hUB hb,hU b hb⟩
  have hUcard := Finset.card_le_card hUsub
  have hforce (w : V) (hwC : w ∈ C) (hwp : w ≠ p) (hwZ : w ∉ Z) : G.Adj p w := by
    by_contra hn
    have hsub : insert w Z ⊆ (C.erase p).filter (fun z => ¬ G.Adj p z) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwp,hwC⟩,hn⟩
      · have hzp : z ≠ p := fun h => hpZ (h ▸ hz)
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzp,hZC hz⟩,
          fun h => hZ z hz h.symm⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwZ] at hcard
    omega
  exact ⟨hforce q hqC hqp hqZ, (hforce y hyC hyp hyZ).symm⟩

theorem in1159_bridge_shore_partition_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C D X Y : Finset V) (x y : V) (k : ℕ)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hk : 3 ≤ k) (hA : A.card=5) (hB : B.card=2*k-5)
    (hXY : Disjoint X Y) (hYA : Disjoint Y A) (hYD : Disjoint Y D)
    (hxA : x ∈ A) (hxX : x ∈ X) (hyC : y ∈ C) (hyY : y ∈ Y)
    (hsize : X.card+Y.card=2*k) (hoddX : Odd X.card) (hoddY : Odd Y.card) :
    let a := (X ∩ A).card; let b0 := (X ∩ B).card; let b1 := (Y ∩ B).card
    let c0 := (X ∩ C).card; let c1 := (Y ∩ C).card; let d := (X ∩ D).card
    1 ≤ a ∧ a ≤ 5 ∧ 1 ≤ c1 ∧ b0+b1+5 ≤ 2*k ∧
    a+b0+b1+c0+c1+d = 2*k ∧ Odd (a+b0+c0+d) ∧ Odd (b1+c1) ∧
    (Y \ B).card=c1 ∧ (Y \ A).card=Y.card ∧ (Y \ D).card=Y.card ∧
    (X \ D).card=a+b0+c0 ∧ ((X.erase x) \ D).card+1=a+b0+c0 := by
  classical
  dsimp only
  have hxc := finset_card_eq_sum_four_block_inter A B C D X hAB hAC hAD hBC hBD hCD hcover
  have hyc := finset_card_eq_sum_four_block_inter A B C D Y hAB hAC hAD hBC hBD hCD hcover
  have hYA0 : Y ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hYA
  have hYD0 : Y ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hYD
  rw [hYA0,hYD0] at hyc
  simp only [Finset.card_empty,zero_add,add_zero] at hyc
  have ha : 1 ≤ (X ∩ A).card := Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxX,hxA⟩⟩
  have ha5 : (X ∩ A).card ≤ 5 := by
    have hh := Finset.card_le_card (Finset.inter_subset_right : X ∩ A ⊆ A)
    omega
  have hc1 : 1 ≤ (Y ∩ C).card := Finset.card_pos.mpr ⟨y,Finset.mem_inter.mpr ⟨hyY,hyC⟩⟩
  have hbd : Disjoint (X ∩ B) (Y ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY)
  have hbcap : (X ∩ B).card + (Y ∩ B).card ≤ B.card := by
    rw [← Finset.card_union_of_disjoint hbd]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
  have hYsub : Y ⊆ B ∪ C := by
    intro z hz
    have hzall : z ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
    simp only [Finset.mem_union] at hzall ⊢
    rcases hzall with ((ha' | hb') | hc') | hd'
    · exact False.elim (Finset.disjoint_left.mp hYA hz ha')
    · exact Or.inl hb'
    · exact Or.inr hc'
    · exact False.elim (Finset.disjoint_left.mp hYD hz hd')
  have hYB : Y \ B = Y ∩ C := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hz,hnB⟩
      rcases Finset.mem_union.mp (hYsub hz) with hzB | hzC
      · exact False.elim (hnB hzB)
      · exact ⟨hz,hzC⟩
    · rintro ⟨hz,hzC⟩
      exact ⟨hz,fun hzB => Finset.disjoint_left.mp hBC hzB hzC⟩
  have hYAc : (Y \ A).card = Y.card := by rw [Finset.sdiff_eq_self_of_disjoint hYA]
  have hYDc : (Y \ D).card = Y.card := by rw [Finset.sdiff_eq_self_of_disjoint hYD]
  have hXDc : (X \ D).card = (X ∩ A).card+(X ∩ B).card+(X ∩ C).card := by
    have hh := Finset.card_sdiff_add_card_inter X D
    omega
  have hxD : x ∉ D := Finset.disjoint_left.mp hAD hxA
  have hxXD : x ∈ X \ D := Finset.mem_sdiff.mpr ⟨hxX,hxD⟩
  have hErase : (X.erase x) \ D = (X \ D).erase x := by ext z; simp [and_comm, and_left_comm, and_assoc]
  have hE : ((X.erase x) \ D).card+1=(X ∩ A).card+(X ∩ B).card+(X ∩ C).card := by
    rw [hErase, Finset.card_erase_add_one hxXD, hXDc]
  refine ⟨ha,ha5,hc1,?_,?_,?_,?_,?_,hYAc,hYDc,hXDc,hE⟩
  · omega
  · omega
  · rw [← hxc]
    exact hoddX
  · rw [← hyc]
    exact hoddY
  · rw [hYB]

theorem in1159_bridge_representative_degree_counts
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y : Finset (Fin (4*k))) (x y : Fin (4*k))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hCD : Disjoint C D)
    (hA : A.card=5) (hB : B.card=2*k-5) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hXY : Disjoint X Y) (hxA : x ∈ A) (hxX : x ∈ X) (hyC : y ∈ C) (hyY : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hYB : (Y \ B).card = (Y ∩ C).card)
    (hYA : (Y \ A).card = Y.card) (hYD : (Y \ D).card = Y.card)
    (hYcard : Y.card = (Y ∩ B).card + (Y ∩ C).card)
    (hXD : (X \ D).card = (X ∩ A).card+(X ∩ B).card+(X ∩ C).card)
    (hXE : ((X.erase x) \ D).card+1 = (X ∩ A).card+(X ∩ B).card+(X ∩ C).card) :
    let a := (X ∩ A).card; let b0 := (X ∩ B).card; let b1 := (Y ∩ B).card
    let c0 := (X ∩ C).card; let c1 := (Y ∩ C).card
    a+b0+c0+2 ≤ c ∧
    (2 ≤ a → c1 ≤ 2) ∧
    (1 ≤ b0 → b1+c1+8 ≤ 2*k) ∧
    (1 ≤ c0 → b1+c1+3 ≤ c) ∧
    (2 ≤ c1 → a+b0+c0+3 ≤ c) := by
  classical
  dsimp only
  have hk : 7 ≤ k := by omega
  have hyD : y ∉ D := Finset.disjoint_left.mp hCD hyC
  have hxB : x ∉ B := Finset.disjoint_left.mp hAB hxA
  have hxC : x ∉ C := Finset.disjoint_left.mp hAC hxA
  have hreverse : ∀ a ∈ Y, ∀ b ∈ X, G.Adj a b → a=y ∧ b=x := by
    intro a ha b hb hab
    have hh := hcross b hb a ha hab.symm
    exact ⟨hh.2,hh.1⟩
  have hsD : Fintype.card (Fin (4*k)) = D.card + (2*k+c-1) + 1 := by
    simp only [Fintype.card_fin]
    omega
  have hdD (v : Fin (4*k)) : 2*k+c-1 ≤ (G.neighborFinset v).card + (c-3) := by
    have hh := hdegree v
    omega
  have hsB : Fintype.card (Fin (4*k)) = B.card + (2*k+4) + 1 := by
    simp only [Fintype.card_fin]
    omega
  have hdB (v : Fin (4*k)) : 2*k+4 ≤ (G.neighborFinset v).card + 2 := by
    have hh := hdegree v
    omega
  have hsA : Fintype.card (Fin (4*k)) = A.card + (4*k-6) + 1 := by
    simp only [Fintype.card_fin]
    omega
  have hdA (v : Fin (4*k)) : 4*k-6 ≤ (G.neighborFinset v).card + (2*k-8) := by
    have hh := hdegree v
    omega
  have hroot := in1159_cross_shore_defect_budget G Y X D y x y hXY.symm hyY hreverse
    hyD (hnoCD y hyC) (2*k+c-1) (c-3) hsD (hdD y)
  have hroot' : (X ∩ A).card + (X ∩ B).card + (X ∩ C).card + 2 ≤ c := by
    omega
  refine ⟨hroot',?_,?_,?_,?_⟩
  · intro hlarge
    have hx : x ∈ X ∩ A := Finset.mem_inter.mpr ⟨hxX,hxA⟩
    have hpos : 0 < ((X ∩ A).erase x).card := by
      rw [Finset.card_erase_of_mem hx]
      omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
    have hv' := Finset.mem_erase.mp hv
    have hvX := (Finset.mem_inter.mp hv'.2).1
    have hvA := (Finset.mem_inter.mp hv'.2).2
    have hvB : v ∉ B := Finset.disjoint_left.mp hAB hvA
    have hb := (in1159_cross_shore_defect_budget G X Y B x y v hXY hvX hcross
      hvB (hnoAB v hvA) (2*k+4) 2 hsB (hdB v)).2 hv'.1
    omega
  · intro hpos
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
    have hvX := (Finset.mem_inter.mp hv).1
    have hvB := (Finset.mem_inter.mp hv).2
    have hvA : v ∉ A := fun h => Finset.disjoint_left.mp hAB h hvB
    have hvx : v ≠ x := fun h => hvA (h.symm ▸ hxA)
    have hanti : ∀ z ∈ A, ¬ G.Adj v z := by
      intro z hz hadj
      exact hnoAB z hz v hvB hadj.symm
    have hb := (in1159_cross_shore_defect_budget G X Y A x y v hXY hvX hcross
      hvA hanti (4*k-6) (2*k-8) hsA (hdA v)).2 hvx
    omega
  · intro hpos
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
    have hvX := (Finset.mem_inter.mp hv).1
    have hvC := (Finset.mem_inter.mp hv).2
    have hvD : v ∉ D := Finset.disjoint_left.mp hCD hvC
    have hvx : v ≠ x := fun h => hxC (h ▸ hvC)
    have hb := (in1159_cross_shore_defect_budget G X Y D x y v hXY hvX hcross
      hvD (hnoCD v hvC) (2*k+c-1) (c-3) hsD (hdD v)).2 hvx
    omega
  · intro hlarge
    have hy : y ∈ Y ∩ C := Finset.mem_inter.mpr ⟨hyY,hyC⟩
    have hpos : 0 < ((Y ∩ C).erase y).card := by
      rw [Finset.card_erase_of_mem hy]
      omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
    have hv' := Finset.mem_erase.mp hv
    have hvY := (Finset.mem_inter.mp hv'.2).1
    have hvC := (Finset.mem_inter.mp hv'.2).2
    have hvD : v ∉ D := Finset.disjoint_left.mp hCD hvC
    have hb := (in1159_cross_shore_defect_budget G Y X D y x v hXY.symm hvY hreverse
      hvD (hnoCD v hvC) (2*k+c-1) (c-3) hsD (hdD v)).2 hv'.1
    omega

theorem in1159_bridge_separator_and_saturated_counts
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k)))
    (A B C D X Y : Finset (Fin (4*k))) (x y p q : Fin (4*k))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hD : D.card=2*k-c)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b) → 2*k ≤ S.card)
    (hXY : Disjoint X Y) (hxX : x ∈ X) (hyY : y ∈ Y) (hyC : y ∈ C)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ a ∈ D, G.Adj x a)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z) :
    (Y ∩ C).card ≤ 3 ∧
    (1 ≤ (X ∩ D).card → (X ∩ D).card + (Y ∩ B).card + c ≤ 2*k) := by
  classical
  have hk : 7 ≤ k := by omega
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hY : Y ⊆ B ∪ {p,q,y} := by
    have hh := in1159_saturated_other_shores_subset G A B C D X Y ∅ x y p q
      hAC hCD hcover hxX hyC hXY (by simp) hcross (by simp) hsatA hsatD hfull
    simpa using hh
  have hYC : Y ∩ C ⊆ ({p,q,y} : Finset (Fin (4*k))) := by
    intro z hz
    have hzY := (Finset.mem_inter.mp hz).1
    have hzC := (Finset.mem_inter.mp hz).2
    rcases Finset.mem_union.mp (hY hzY) with hzB | hzthree
    · exact False.elim (Finset.disjoint_left.mp hBC hzB hzC)
    · exact hzthree
  have hthree : ({p,q,y} : Finset (Fin (4*k))).card ≤ 3 := by
    calc
      ({p,q,y} : Finset (Fin (4*k))).card ≤ ({q,y} : Finset (Fin (4*k))).card + 1 := Finset.card_insert_le _ _
      _ ≤ 3 := by have hh := (Finset.card_le_two : ({q,y} : Finset (Fin (4*k))).card ≤ 2); omega
  constructor
  · exact (Finset.card_le_card hYC).trans hthree
  · intro hd
    have hDpos : (D ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.inter_comm]
      omega
    have hXW : Disjoint X (Y.erase y) :=
      Finset.disjoint_of_subset_right (Finset.erase_subset y Y) hXY
    have hanti : ∀ a ∈ X, ∀ b ∈ Y.erase y, ¬ G.Adj a b := by
      intro a ha b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hcross a ha b hb'.2 hab).2
    have hABsize : A.card+B.card=2*k := by omega
    have hh := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) hABsize hnoCD hsep
      X (Y.erase y) hXW hanti hDpos
    have hBY : B ∩ Y.erase y = B ∩ Y := by
      ext z
      simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hzB,_,hzY⟩
        exact ⟨hzB,hzY⟩
      · rintro ⟨hzB,hzY⟩
        exact ⟨hzB,fun h => hyB (h ▸ hzB),hzY⟩
    rw [hBY,Finset.inter_comm D X,Finset.inter_comm B Y] at hh
    omega

theorem in1159_bridge_connected_block_one_shore
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (B C X Y : Finset V) (x y : V)
    (hBC : Disjoint B C) (hyC : y ∈ C) (hXY : Disjoint X Y)
    (hconn : (G.induce {z | z ∈ B}).Connected)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hfull : (X ∩ B).card + (Y ∩ B).card = B.card) :
    (X ∩ B).card = 0 ∨ (Y ∩ B).card = 0 := by
  classical
  have hdis : Disjoint (X ∩ B) (Y ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY)
  have hsub : (X ∩ B) ∪ (Y ∩ B) ⊆ B :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hcover : (X ∩ B) ∪ (Y ∩ B) = B := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_union_of_disjoint hdis]
    omega
  have hclosed : ∀ a ∈ X, ∀ b ∈ B, G.Adj a b → b ∈ X := by
    intro a ha b hb hab
    have hb' : b ∈ (X ∩ B) ∪ (Y ∩ B) := by rw [hcover]; exact hb
    rcases Finset.mem_union.mp hb' with hbX | hbY
    · exact (Finset.mem_inter.mp hbX).1
    · have hbY' := (Finset.mem_inter.mp hbY).1
      have heq := (hcross a ha b hbY' hab).2
      exact False.elim (Finset.disjoint_left.mp hBC (heq ▸ hb) hyC)
  by_cases hx : (X ∩ B).Nonempty
  · by_cases hy : (Y ∩ B).Nonempty
    · obtain ⟨u,hu⟩ := hx
      obtain ⟨v,hv⟩ := hy
      have huX := (Finset.mem_inter.mp hu).1
      have huB := (Finset.mem_inter.mp hu).2
      have hvY := (Finset.mem_inter.mp hv).1
      have hvB := (Finset.mem_inter.mp hv).2
      let u' : {z // z ∈ B} := ⟨u,huB⟩
      let v' : {z // z ∈ B} := ⟨v,hvB⟩
      have hwalk : ∀ (a b : {z // z ∈ B}),
          (G.induce {z | z ∈ B}).Reachable a b → a.1 ∈ X → b.1 ∈ X := by
        intro a b hab
        obtain ⟨p⟩ := hab
        induction p with
        | nil => intro ha; exact ha
        | cons hadj p ih =>
          intro ha
          rename_i a' m b'
          exact ih (hclosed a'.1 ha m.1 m.2 (by simpa using hadj))
      have hvX : v ∈ X := hwalk u' v' (hconn u' v') huX
      exact False.elim (Finset.disjoint_left.mp hXY hvX hvY)
    · right
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hy)
  · left
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hx)

/-!
# in1159_bridge_small_without_criticality

Topic: graphs   Node: 43333cf784ac

Provenance: helper lemma. OP-1957: small arithmetic core for the unbounded saturated small-shore count reduction.

The displayed natural-number endpoint, degree, separator and B-component inequalities force one of the two stated small-shore count patterns.
-/

set_option maxHeartbeats 2000000

theorem in1159_bridge_small_without_criticality
    (k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (ha : 1 ≤ a ∧ a ≤ 2) (hc1 : 1 ≤ c1)
    (he2 : (c2 = 0 ∧ b2 = 0) ∨ 1 ≤ c2)
    (he3 : (c3 = 0 ∧ b3 = 0) ∨ 1 ≤ c3)
    (hodd0 : Odd (a+b0+c0+d)) (hodd1 : Odd (b1+c1))
    (hs : m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + 1 ≤ c)
    (hb : b0+b1+b2+b3+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+b2+b3+eb+c0+c1+c2+c3+d+m+
      (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) = 2*k)
    (hsmall : c1+c2+c3 ≤ 3)
    (hrooty : a+b0+c0+b2+c2+b3+c3+eb+2 ≤ c)
    (hrepA : 2 ≤ a → c1+c2+c3 ≤ 2)
    (hrep0C : 1 ≤ c0 → b1+b2+b3+eb+c1+c2+c3+3 ≤ c)
    (hcutD : 1 ≤ d → d+b1+b2+b3+eb+c ≤ 2*k)
    (hrep1C : 2 ≤ c1 → a+b0+b2+b3+eb+c0+c2+c3+3 ≤ c)
    (hrep2C : 1 ≤ c2 → a+b0+b1+b3+eb+c0+c1+c3+3 ≤ c)
    (hrep3C : 1 ≤ c3 → a+b0+b1+b2+eb+c0+c1+c2+3 ≤ c)
    (hm : m=0) (heb0 : eb=0) (hb2 : b2=0) (hb3 : b3=0)
    (hc2 : c2=0) (hc3 : c3=0)
    :
    a=1 ∧ ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
      (c1=1 ∧ c2+c3=2 ∧ (1 ≤ c2 → c2=1 ∧ b2+c2=1) ∧
        (1 ≤ c3 → c3=1 ∧ b3+c3=1))) := by
  subst m
  subst eb
  subst b2
  subst b3
  subst c2
  subst c3
  obtain ⟨t0,ht0⟩ := hodd0
  obtain ⟨t1,ht1⟩ := hodd1
  simp_all
  all_goals omega

theorem boundary_five_odd_saturated_two_odd_shores_force_patterns
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (x p q : Fin (4*k)) (hx : x ∈ A)
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (y : Fin (4*k)) (hy : y ∈ C) (hyp : y ≠ p) (hyq : y ≠ q)
    (X Y : Finset (Fin (4*k))) (hXY : Disjoint X Y)
    (hsize : X.card + Y.card = 2*k) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y) :
    (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ U ⊆ A.erase x, U.card=2 ∧
      ∀ a ∈ U, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) ∨
    (G.Adj p q ∧ (G.Adj y p ∨ G.Adj y q) ∧
      ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=c-4 ∧
        (∀ b ∈ U, ¬ G.Adj b p ∧ ¬ G.Adj b q ∧ ¬ G.Adj b y) ∧
        (∀ z ∈ Z, ¬ G.Adj z p ∧ ¬ G.Adj z q ∧ ¬ G.Adj z y)) := by
  classical
  have hk : 7 ≤ k := by omega
  obtain ⟨hYA,hYD,_,_⟩ := saturated_barrier_other_shores_avoid_outer_blocks
    G A C D X Y ∅ x y hAC hCD hXY (by simp) hxX hyY hy hcross (by simp) hsatA hsatD
  obtain ⟨ha1,ha5,hc1,hBcap,htotal,hodd0,hodd1,hYB,hYAc,hYDc,hXD,hXE⟩ :=
    in1159_bridge_shore_partition_counts A B C D X Y x y k hAB hAC hAD hBC hBD hCD
      hcover (by omega) hA hB hXY hYA hYD hx hxX hy hyY hsize hoddX hoddY
  have hYcard : Y.card = (Y ∩ B).card+(Y ∩ C).card := by
    have hh := finset_card_eq_sum_four_block_inter A B C D Y hAB hAC hAD hBC hBD hCD hcover
    have hYA0 := Finset.disjoint_iff_inter_eq_empty.mp hYA
    have hYD0 := Finset.disjoint_iff_inter_eq_empty.mp hYD
    rw [hYA0,hYD0] at hh
    simpa using hh
  obtain ⟨hrooty,hrepA,hrepB,hrep0C,hrep1C⟩ :=
    in1159_bridge_representative_degree_counts k c hc hkc G A B C D X Y x y
      hAB hAC hCD hA hB hD hnoAB hnoCD hdegree hXY hx hxX hy hyY hcross
      hYB hYAc hYDc hYcard hXD hXE
  obtain ⟨hsmall,hcutD⟩ := in1159_bridge_separator_and_saturated_counts k c hc hkc
    G A B C D X Y x y p q hAB hAC hAD hBC hBD hCD hcover hA hB hD hnoCD hsep
    hXY hxX hyY hy hcross hsatA hsatD hfull
  by_cases hfive : (X ∩ A).card=5
  · right
    left
    have hAX : X ∩ A = A := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      omega
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hvX : v ∈ X := by
      have hh : v ∈ X ∩ A := by rw [hAX]; exact hv'.2
      exact (Finset.mem_inter.mp hh).1
    intro hadj
    exact hv'.1 (hcross v hvX y hyY hadj).1
  · have hale4 : (X ∩ A).card ≤ 4 := by omega
    by_cases hlarge : 3 ≤ (X ∩ A).card
    · left
      have hcy : 2 ≤ (Y ∩ C).card := by
        by_contra hn
        have hc1eq : (Y ∩ C).card=1 := by omega
        have hcrit :
            ((X ∩ B).card+(Y ∩ B).card+0+5 < 2*k →
              0+(X ∩ B).card+(Y ∩ B).card+0+6 ≤ 2*k) ∧
            ((X ∩ B).card+(Y ∩ B).card+0+5 = 2*k → 0 ≤ 1 ∧
              (if 1 ≤ (X ∩ B).card then 1 else 0) +
              (if 1 ≤ (Y ∩ B).card then 1 else 0) + 0 ≤ 1) := by
          constructor
          · intro hh
            omega
          · intro hh
            have hfullB : (X ∩ B).card + (Y ∩ B).card = B.card := by omega
            obtain h0 | h1 := in1159_bridge_connected_block_one_shore G B C X Y x y
              hBC hy hXY hconnB hcross hfullB
            · simp [h0] <;> split_ifs <;> omega
            · simp [h1] <;> split_ifs <;> omega
        have hf := five_odd_saturated_large_shore_arithmetic_core k c 0 0
          (X ∩ A).card (X ∩ B).card (Y ∩ B).card (X ∩ C).card (X ∩ D).card
          hc hkc (by omega) ⟨hlarge,hale4⟩ hodd0 (by omega) (by omega) (by omega)
          (by intro hh; have h := hrepB hh; omega)
          (by intro hh; have h := hrep0C hh; omega)
          (by intro hh; have h := hcutD hh; omega) hcrit
        exact hf.elim
      exact in1159_large_shore_two_common_defects G A C X Y x y p q
        hx hxX hyY hcross hfull (by simpa [Finset.inter_comm] using hlarge)
        (by simpa [Finset.inter_comm] using hcy)
    · have hasmall : 1 ≤ (X ∩ A).card ∧ (X ∩ A).card ≤ 2 := by omega
      have hsmallcore := in1159_bridge_small_without_criticality k c 0 0
        (X ∩ A).card (X ∩ B).card (Y ∩ B).card 0 0 (X ∩ C).card
        (Y ∩ C).card 0 0 (X ∩ D).card hc hkc (by omega) hasmall hc1
        (by simp) (by simp) hodd0 hodd1 (by simp; omega) (by omega) (by simp; omega)
        (by omega) (by omega) (by intro hh; have h := hrepA hh; omega)
        (by intro hh; have h := hrep0C hh; omega)
        (by intro hh; have h := hcutD hh; omega)
        (by intro hh; have h := hrep1C hh; omega)
        (by simp) (by simp) rfl rfl rfl rfl rfl rfl
      have hc1three : (Y ∩ C).card=3 := by
        rcases hsmallcore with ⟨_,h | h⟩
        · exact h.1
        · omega
      have hdefect : (X ∩ B).card + (X ∩ C).card = c-4 := by
        rcases hsmallcore with ⟨_,h | h⟩
        · omega
        · omega
      have hYCsub : Y ∩ C ⊆ ({p,q,y} : Finset (Fin (4*k))) := by
        intro z hz
        have hzY := (Finset.mem_inter.mp hz).1
        have hzC := (Finset.mem_inter.mp hz).2
        by_cases hzp : z=p
        · simp [hzp]
        · by_cases hzq : z=q
          · simp [hzq]
          · have hzy := (hcross x hxX z hzY (hfull z hzC hzp hzq)).2
            simp [hzy]
      have hthree : ({p,q,y} : Finset (Fin (4*k))).card=3 := by
        simp [hpq,Ne.symm hpq,hyp,Ne.symm hyp,hyq,Ne.symm hyq]
      have hYCeq : Y ∩ C = ({p,q,y} : Finset (Fin (4*k))) := by
        apply Finset.eq_of_subset_of_card_le hYCsub
        omega
      have hpY : p ∈ Y := by
        have hh : p ∈ Y ∩ C := by rw [hYCeq]; simp
        exact (Finset.mem_inter.mp hh).1
      have hqY : q ∈ Y := by
        have hh : q ∈ Y ∩ C := by rw [hYCeq]; simp
        exact (Finset.mem_inter.mp hh).1
      have hpZ : p ∉ X ∩ C := fun h => Finset.disjoint_left.mp hXY (Finset.mem_inter.mp h).1 hpY
      have hqZ : q ∉ X ∩ C := fun h => Finset.disjoint_left.mp hXY (Finset.mem_inter.mp h).1 hqY
      have hyZ : y ∉ X ∩ C := fun h => Finset.disjoint_left.mp hXY (Finset.mem_inter.mp h).1 hyY
      have hxB : x ∉ B := Finset.disjoint_left.mp hAB hx
      have hxC : x ∉ C := Finset.disjoint_left.mp hAC hx
      have hU (v : Fin (4*k)) (hv : v ∈ X ∩ B) (w : Fin (4*k)) (hw : w ∈ Y) : ¬ G.Adj v w := by
        intro hadj
        have he := (hcross v (Finset.mem_inter.mp hv).1 w hw hadj).1
        exact hxB (he ▸ (Finset.mem_inter.mp hv).2)
      have hZ (v : Fin (4*k)) (hv : v ∈ X ∩ C) (w : Fin (4*k)) (hw : w ∈ Y) : ¬ G.Adj v w := by
        intro hadj
        have he := (hcross v (Finset.mem_inter.mp hv).1 w hw hadj).1
        exact hxC (he ▸ (Finset.mem_inter.mp hv).2)
      obtain ⟨_,hcols,_⟩ := boundary_five_odd_saturated_incidence_budgets k c hc hkc G A B C D
        hAB hAC hAD hBC hBD hCD hA hB hC hD hnoAB hnoCD hdegree hsep x p q hx hp hq hxp hxq
      have hbudget : (B.filter (fun b => ¬ G.Adj b p)).card +
          ((C.erase p).filter (fun z => ¬ G.Adj p z)).card + 1 ≤ c-3 := by
        have hh := hcols p hp
        simp at hh
        omega
      have hedges := in1159_tight_defect_budget_forces_two_edges G B C (X ∩ B) (X ∩ C) p q y c
        (by omega) hq hy (Ne.symm hpq) hyp hpZ hqZ hyZ Finset.inter_subset_right
        Finset.inter_subset_right (fun v hv => hU v hv p hpY) (fun v hv => hZ v hv p hpY)
        hdefect hbudget
      right
      right
      refine ⟨hedges.1,Or.inl hedges.2,X ∩ B,Finset.inter_subset_right,X ∩ C,?_,hdefect,?_,?_⟩
      · intro z hz
        have hzX := (Finset.mem_inter.mp hz).1
        have hzC := (Finset.mem_inter.mp hz).2
        refine Finset.mem_sdiff.mpr ⟨hzC,?_⟩
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨fun h => Finset.disjoint_left.mp hXY (h ▸ hzX) hpY,
          fun h => Finset.disjoint_left.mp hXY (h ▸ hzX) hqY,
          fun h => Finset.disjoint_left.mp hXY (h ▸ hzX) hyY⟩
      · intro v hv
        exact ⟨hU v hv p hpY,hU v hv q hqY,hU v hv y hyY⟩
      · intro v hv
        exact ⟨hZ v hv p hpY,hZ v hv q hqY,hZ v hv y hyY⟩
