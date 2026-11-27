import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalBlockAmbientOddComponentsBound
import AFTD.Kb.Tcs.SimpleGraphOddComponentsCardLeVertices
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# op1957_saturated_b_only_connected_shore_impossible

Topic: graphs   Node: 7f1eba7ef7b3

Provenance: helper lemma. OP-1957: saturated-block boundary reduction, arXiv:2611.22690 and arXiv:1011.3384

The displayed disjoint connected endpoint shores and B-only odd reservoir cannot satisfy the four-block degree, separator and factor-criticality conditions.
-/

theorem op1957_saturated_b_only_connected_shore_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k c s : ℕ)
    (hc : 3 ≤ c) (hkc : c ≤ k) (hV : Fintype.card V=4*k)
    (A B C D X Y U : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : 3 ≤ A.card) (hsizeAB : A.card+B.card=2*k)
    (hC : C.card=c) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset V, P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x y : V) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hXA : X ∩ A = {x}) (hY : Y ⊆ B ∪ {y}) (hUB : U ⊆ B)
    (hsize : X.card+Y.card+U.card+s=2*k) (hs : 1 ≤ s)
    (hodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u)
    (hreach : ∀ z (hz : z ∈ X), (G.induce {a | a ∈ X}).Reachable ⟨x,hxX⟩ ⟨z,hz⟩) : False := by
  classical
  let L := (Y ∩ B) ∪ U
  let t := (X ∩ B).card+(X ∩ C).card
  let v := (X ∩ D).card
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hyC h
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hxA h
  have hxC : x ∉ C := fun h => Finset.disjoint_left.mp hAC hxA h
  have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hAD hxA h
  have hxY : x ∉ Y := fun h => Finset.disjoint_left.mp hXY hxX h
  have hyX : y ∉ X := fun h => Finset.disjoint_left.mp hXY h hyY
  have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hYU hyY h
  have hLU : U ⊆ L := by intro z hz; exact Finset.mem_union_right _ hz
  have hLB : L ⊆ B := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_inter.mp hz).2
    · exact hUB hz
  have hLYU : Disjoint (Y ∩ B) U := Finset.disjoint_of_subset_left Finset.inter_subset_left hYU
  have hLcard : L.card=(Y ∩ B).card+U.card := Finset.card_union_of_disjoint hLYU
  have hXL : Disjoint X L := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨Finset.disjoint_of_subset_right Finset.inter_subset_left hXY,hXU⟩
  have hantiXL : ∀ a ∈ X, ∀ b ∈ L, ¬ G.Adj a b := by
    intro a ha b hb hab
    rcases Finset.mem_union.mp hb with hb | hb
    · have hb' := Finset.mem_inter.mp hb
      have he := hcross a ha b hb'.1 hab
      exact hyB (he.2 ▸ hb'.2)
    · exact hantiX a ha b hb hab
  have hYeq : Y=(Y ∩ B) ∪ {y} := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp (hY hz) with hb | hy
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz,hb⟩)
      · exact Finset.mem_union_right _ hy
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · have hz' := Finset.mem_singleton.mp hz
        simpa [hz'] using hyY
  have hYcard : Y.card=(Y ∩ B).card+1 := by
    calc
      Y.card = ((Y ∩ B) ∪ {y}).card := congrArg Finset.card hYeq
      _ = (Y ∩ B).card+1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · simp [Finset.disjoint_singleton_right,hyB]
  have hXparts := finset_card_eq_sum_four_block_inter A B C D X hAB hAC hAD hBC hBD hCD hcover
  have hXcard : X.card=1+t+v := by
    have hXAcard := congrArg Finset.card hXA
    simp only [Finset.card_singleton] at hXAcard
    dsimp [t,v]
    omega
  have hsize' : L.card+v+s+t+2=2*k := by omega
  have hUBD : Disjoint U D := Finset.disjoint_of_subset_left hUB hBD
  have hXB_U : Disjoint (X ∩ B) U := Finset.disjoint_of_subset_left Finset.inter_subset_left hXU
  have hXC_U : Disjoint (X ∩ C) U := Finset.disjoint_of_subset_left Finset.inter_subset_left hXU
  have hXB_XC : Disjoint (X ∩ B) (X ∩ C) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right (Finset.disjoint_of_subset_right Finset.inter_subset_right hBC)
  have hSU : s ≤ U.card := by
    have hh := simple_graph_odd_components_card_le_vertices (G.induce {v | v ∈ U})
    have hcard : Fintype.card {v : V | v ∈ U}=U.card := by simp
    rw [hcard] at hh
    omega
  have hbudget : U.card+t+3 ≤ c := by
    have hs' : ∀ z, (z ∈ U ∨ z ∈ X ∩ B ∨ z ∈ X ∩ C ∨ z ∈ (∅ : Finset V)) → z ≠ y ∧ ¬ G.Adj y z := by
      intro z hz
      rcases hz with hz | hz | hz | hz
      · exact ⟨fun h => hyU (h ▸ hz),hantiY y hyY z hz⟩
      · have hz' := Finset.mem_inter.mp hz
        refine ⟨fun h => hyX (h ▸ hz'.1),?_⟩
        intro hadj
        have he := (hcross z hz'.1 y hyY hadj.symm).1
        exact hxB (he ▸ hz'.2)
      · have hz' := Finset.mem_inter.mp hz
        refine ⟨fun h => hyX (h ▸ hz'.1),?_⟩
        intro hadj
        have he := (hcross z hz'.1 y hyY hadj.symm).1
        exact hxC (he ▸ hz'.2)
      · simp at hz
    have hh := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G D y hyD (hnoCD y hyC)
      (2*k+c-1) (c-3) (by omega) (by have := hdegree y; omega)
      U (X ∩ B) (X ∩ C) ∅ hs' hXB_U.symm hXC_U.symm (by simp) hXB_XC (by simp) (by simp)
    have hUD : U \ D = U := Finset.sdiff_eq_self_of_disjoint hUBD
    have hXBD : (X ∩ B) \ D = X ∩ B := Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_of_subset_left Finset.inter_subset_right hBD)
    have hXCD : (X ∩ C) \ D = X ∩ C := Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_of_subset_left Finset.inter_subset_right hCD)
    simp only [hUD,hXBD,hXCD,Finset.empty_sdiff,Finset.card_empty,add_zero] at hh
    dsimp [t]
    omega
  have hv0 : v=0 := by
    by_contra hn
    have hd : (D ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      dsimp [v] at hn
      have : 0 < (X ∩ D).card := by omega
      simpa [Finset.inter_comm] using this
    have hb := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) hsizeAB hnoCD hsep X L hXL hantiXL hd
    have hBL : B ∩ L=L := Finset.inter_eq_right.mpr hLB
    have hDL : D ∩ L=∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_right hLB hBD.symm)
    rw [hBL,hDL,Finset.card_empty,add_zero,Finset.inter_comm D X] at hb
    dsimp [v] at *
    omega
  have hLlarge : c-3 < L.card := by omega
  by_cases ht : t=0
  · have hybudget := anticomplete_neighbor_defect_bound G D y hyD (hnoCD y hyC)
      (2*k+c-1) (c-3) (by omega) (by have := hdegree y; omega)
    have hnot : ¬ (∀ z ∈ L, ¬ G.Adj y z) := by
      intro hall
      have hsub : L ⊆ (((Finset.univ \ D).erase y) \ G.neighborFinset y) := by
        intro z hz
        have hzB := hLB hz
        have hzD : z ∉ D := fun hd => Finset.disjoint_left.mp hBD hzB hd
        have hzy : z ≠ y := fun he => hyB (he ▸ hzB)
        simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
        exact ⟨⟨hzy,hzD⟩,hall z hz⟩
      have hh := Finset.card_le_card hsub
      omega
    push Not at hnot
    obtain ⟨z,hzL,hyz⟩ := hnot
    have hzB := hLB hzL
    have hzU : z ∉ U := fun hz => hantiY y hyY z hz hyz
    have hanti : ∀ u ∈ U, ∀ w ∈ B ∩ L, w ∉ U → ¬ G.Adj u w := by
      intro u hu w hw hwU hadj
      have hwL := (Finset.mem_inter.mp hw).2
      rcases Finset.mem_union.mp hwL with hwY | hwU'
      · exact hantiY w (Finset.mem_inter.mp hwY).1 u hu hadj.symm
      · exact hwU hwU'
    have hh := op1957_factorcritical_block_ambient_odd_components_bound G B U L hcritB hUB hLU z hzB hzL hzU hanti
    have hcard := Finset.card_sdiff_add_card_eq_card hLB
    omega
  · have htpos : 0 < t := by omega
    have hXgt : 1 < X.card := by omega
    have hnot : ¬ X ⊆ {x} := by
      intro hh
      have hc' := Finset.card_le_card hh
      simp at hc'
      omega
    obtain ⟨w,hwX,hwx⟩ := Finset.not_subset.mp hnot
    have hwne : w ≠ x := by simpa using hwx
    have hne : (⟨x,hxX⟩ : {a // a ∈ X}) ≠ ⟨w,hwX⟩ := by intro h; exact hwne (congrArg Subtype.val h).symm
    have hre := hreach w hwX
    obtain ⟨z,hxz⟩ := SimpleGraph.Reachable.nonempty_neighborSet_left hne hre
    have hzX : z.val ∈ X := z.property
    have hxzG : G.Adj x z.val := hxz
    have hzx : z.val ≠ x := hxzG.ne.symm
    have hzA : z.val ∉ A := by
      intro hzA
      have hzXA : z.val ∈ X ∩ A := Finset.mem_inter.mpr ⟨hzX,hzA⟩
      rw [hXA] at hzXA
      exact hzx (Finset.mem_singleton.mp hzXA)
    have hzB : z.val ∉ B := fun hz => hnoAB x hxA z.val hz hxzG
    have hzD : z.val ∉ D := by
      intro hz
      have hp : 0 < (X ∩ D).card := Finset.card_pos.mpr ⟨z.val,Finset.mem_inter.mpr ⟨hzX,hz⟩⟩
      dsimp [v] at hv0
      omega
    have hzC : z.val ∈ C := by
      have hzcover : z.val ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
      simp only [Finset.mem_union] at hzcover
      rcases hzcover with ((ha | hb) | hc') | hd
      · exact False.elim (hzA ha)
      · exact False.elim (hzB hb)
      · exact hc'
      · exact False.elim (hzD hd)
    have hzy : z.val ≠ y := fun he => hyX (he ▸ hzX)
    have hzL : z.val ∉ L := fun h => Finset.disjoint_left.mp hXL hzX h
    have hyL : y ∉ L := fun h => hyB (hLB h)
    have hzyanti : ¬ G.Adj z.val y := fun h => hzx (hcross z.val hzX y hyY h).1
    have hs' : ∀ w, (w ∈ L ∨ w ∈ ({y} : Finset V) ∨ w ∈ (∅ : Finset V) ∨ w ∈ (∅ : Finset V)) → w ≠ z.val ∧ ¬ G.Adj z.val w := by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · exact ⟨fun he => hzL (he ▸ hw),hantiXL z.val hzX w hw⟩
      · have he := Finset.mem_singleton.mp hw
        subst w
        exact ⟨hzy.symm,hzyanti⟩
      · simp at hw
      · simp at hw
    have hLD : Disjoint L D := Finset.disjoint_of_subset_left hLB hBD
    have hbudget' := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G D z.val hzD (hnoCD z.val hzC)
      (2*k+c-1) (c-3) (by omega) (by have := hdegree z.val; omega)
      L {y} ∅ ∅ hs' (by simpa [Finset.disjoint_singleton_right] using hyL) (by simp) (by simp) (by simp) (by simp) (by simp)
    have hLD' : L \ D=L := Finset.sdiff_eq_self_of_disjoint hLD
    have hyD' : ({y} : Finset V) \ D={y} := Finset.sdiff_eq_self_of_disjoint (by simp [Finset.disjoint_singleton_left,hyD])
    simp only [hLD',hyD',Finset.card_singleton,Finset.empty_sdiff,Finset.card_empty,add_zero] at hbudget'
    omega
