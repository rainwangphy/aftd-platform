import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierComponentPartition
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.Supp
import AFTD.Kb.Tcs.F

/-!
# forced_matching_edge_barrier_partition_with_odd_endpoints

Topic: graphs   Node: b035c06349d3

Provenance: helper lemma. OP-1957: expose endpoint parity from the existing Tutte-barrier proof.

A matched forced edge with an alternate path has the displayed positive barrier and anticomplete component partition, with both endpoint components of odd cardinality.
-/

set_option maxHeartbeats 3000000

theorem in1158_odd_reservoir_local
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (S U : Finset V) (hSU : Disjoint S U)
    (hanti : ∀ u ∈ U, ∀ v, v ∉ U → v ∉ S → ¬ G.Adj u v)
    (hodd : S.card ≤ (G.induce {v | v ∈ U}).oddComponents.ncard) :
    ∀ s ∈ S, ∃ u ∈ U, P.Adj s u := by
  classical
  set GU := G.induce {v | v ∈ U} with hGU
  let ι : ↥{v | v ∈ U} → V := Subtype.val
  have hι : Function.Injective ι := Subtype.val_injective
  have hkey : ∀ c ∈ GU.oddComponents, ∃ b : V, b ∈ S ∧ ∃ a ∈ c.supp, P.Adj (ι a) b := by
    intro c hc
    by_contra hno
    push Not at hno
    let C : Set V := ι '' c.supp
    have hmatch : (P.induce C).IsMatching := by
      intro x hx
      obtain ⟨a', ha', rfl⟩ := hx
      obtain ⟨b, hab, huniq⟩ := hP.1 (hP.2 (ι a'))
      have hGab : G.Adj a'.1 b := P.adj_sub hab
      have hbU : b ∈ U := by
        by_contra hbU
        by_cases hbS : b ∈ S
        · exact hno b hbS a' ha' hab
        · exact hanti a'.1 a'.2 b hbU hbS hGab
      let b' : ↥{v | v ∈ U} := ⟨b,hbU⟩
      have hGUadj : GU.Adj a' b' := by simpa [GU] using hGab
      have hbc : b' ∈ c.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha' ⊢
        rw [← ha']
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hGUadj).symm
      have hbι : ι b' = b := rfl
      refine ⟨b, ⟨⟨a',ha',rfl⟩, ⟨b',hbc,hbι⟩, hab⟩, fun y hy => huniq y hy.2.2⟩
    have hfin : Fintype (P.induce C).verts := Fintype.ofFinite _
    have he := hmatch.even_card
    rw [← Set.ncard_eq_toFinset_card'] at he
    have hC : (P.induce C).verts.ncard = c.supp.ncard := by
      show C.ncard = _
      exact Set.ncard_image_of_injective _ hι
    rw [hC] at he
    exact (Nat.not_even_iff_odd.mpr hc) he
  let f : GU.oddComponents → {v : V // v ∈ S} := fun c =>
    ⟨(hkey c.val c.property).choose, (hkey c.val c.property).choose_spec.1⟩
  have hinj : Function.Injective f := by
    intro c1 c2 heq
    obtain ⟨_, a1, ha1, hm1⟩ := (hkey c1.val c1.property).choose_spec
    obtain ⟨_, a2, ha2, hm2⟩ := (hkey c2.val c2.property).choose_spec
    have e : (hkey c1.val c1.property).choose = (hkey c2.val c2.property).choose := by
      exact congrArg Subtype.val heq
    rw [e] at hm1
    have hw : (hkey c2.val c2.property).choose ∈ P.verts := P.edge_vert hm1.symm
    have h12 : ι a1 = ι a2 := (hP.1 hw).unique hm1.symm hm2.symm
    have ha : a1 = a2 := hι h12
    apply Subtype.ext
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha1 ha2
    rw [← ha1,← ha2,ha]
  have hcard : Fintype.card {v : V // v ∈ S} ≤ Fintype.card GU.oddComponents := by
    have hc : GU.oddComponents.ncard = Fintype.card GU.oddComponents := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    simpa only [Fintype.card_coe, ← hc] using hodd
  have hsurj : Function.Surjective f := by
    have hle := Fintype.card_le_of_injective f hinj
    exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, Nat.le_antisymm hle hcard⟩).2
  intro s hs
  obtain ⟨c,hc⟩ := hsurj ⟨s,hs⟩
  obtain ⟨_,u,hu,hPu⟩ := (hkey c.val c.property).choose_spec
  have heq : (hkey c.val c.property).choose = s := congrArg Subtype.val hc
  exact ⟨u.val,u.property,heq ▸ hPu.symm⟩



theorem in1158_single_exit_local
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (X : Finset V) (x y : V)
    (hx : x ∈ X) (hy : y ∉ X) (hxy : P.Adj x y)
    (hclosed : ∀ a ∈ X, ∀ b, P.Adj a b → b ∉ X → a=x ∧ b=y) : Odd X.card := by
  classical
  let F : Finset V := X.erase x
  let C : Set V := F
  have hmatch : (P.induce C).IsMatching := by
    intro a ha
    have haF : a ∈ F := ha
    have haX : a ∈ X := (Finset.mem_erase.mp haF).2
    have hax : a ≠ x := (Finset.mem_erase.mp haF).1
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
    have hbx : b ≠ x := by
      intro he
      subst b
      have hay : a = y := (hP.1 (hP.2 x)).unique hab.symm hxy
      exact hy (hay ▸ haX)
    have hbX : b ∈ X := by
      by_contra hbX
      exact hax (hclosed a haX b hab hbX).1
    have hbF : b ∈ F := Finset.mem_erase.mpr ⟨hbx,hbX⟩
    refine ⟨b,⟨haF,hbF,hab⟩,?_⟩
    intro z hz
    exact huniq z hz.2.2
  have he := hmatch.even_card
  rw [← Set.ncard_eq_toFinset_card'] at he
  have hF : (P.induce C).verts.ncard = F.card := by
    show C.ncard = _
    simp [C]
  rw [hF] at he
  have hcard : F.card + 1 = X.card := Finset.card_erase_add_one hx
  obtain ⟨n,hn⟩ := he
  apply Nat.odd_iff.mpr
  omega

theorem forced_matching_edge_barrier_partition_with_odd_endpoints
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : G.Adj u v)
    (hP : ∃ P : G.Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching)
    (hpath : (G.deleteEdges {s(u,v)}).Reachable u v) :
    ∃ S X Y U : Finset V,
      S.Nonempty ∧ Disjoint S X ∧ Disjoint S Y ∧ Disjoint S U ∧
      Disjoint X Y ∧ Disjoint X U ∧ Disjoint Y U ∧
      S ∪ X ∪ Y ∪ U = Finset.univ ∧ u ∈ X ∧ v ∈ Y ∧
      (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y → x = u ∧ y = v) ∧
      (∀ w ∈ U, ∀ z ∈ X ∪ Y, ¬ G.Adj w z) ∧
      S.card ≤ (G.induce {a | a ∈ U}).oddComponents.ncard ∧ Odd X.card ∧ Odd Y.card := by
  classical
  obtain ⟨P,hP⟩ := hP
  obtain ⟨S,X,Y,U,hSne,hSX,hSY,hSU,hXY,hXU,hYU,hcover,huX,hvY,hcross,hanti,hoddU⟩ :=
    forced_matching_edge_barrier_component_partition G u v huv ⟨P,hP⟩ hforced hpath
  have hPuv : P.Adj u v := by
    by_contra hnot
    have hsub : ∀ a b, P.Adj a b → (G.deleteEdges {s(u,v)}).Adj a b := by
      intro a b hab
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨P.adj_sub hab, ?_⟩
      simp only [Set.mem_singleton_iff,not_false_eq_true]
      intro he
      rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact hnot (ha ▸ hb ▸ hab)
      · exact hnot (hb ▸ ha ▸ hab.symm)
    let Q : (G.deleteEdges {s(u,v)}).Subgraph :=
      ⟨P.verts,P.Adj,(fun {a b} hab => hsub a b hab),P.edge_vert,P.symm⟩
    have hQ : Q.IsPerfectMatching := ⟨hP.1,hP.2⟩
    exact hforced ⟨Q,hQ⟩
  have hUanti : ∀ w ∈ U, ∀ z, z ∉ U → z ∉ S → ¬ G.Adj w z := by
    intro w hw z hzU hzS
    have hz : z ∈ S ∪ X ∪ Y ∪ U := by rw [hcover]; exact Finset.mem_univ z
    simp only [Finset.mem_union] at hz
    have hzXY : z ∈ X ∪ Y := by
      simp only [Finset.mem_union]
      rcases hz with ((hz|hz)|hz)|hz
      · exact False.elim (hzS hz)
      · exact Or.inl hz
      · exact Or.inr hz
      · exact False.elim (hzU hz)
    exact hanti w hw z hzXY
  have hres : ∀ s ∈ S, ∃ w ∈ U, P.Adj s w :=
    in1158_odd_reservoir_local G P hP S U hSU hUanti hoddU
  have hnotS : ∀ a ∈ X ∪ Y, ∀ b ∈ S, P.Adj a b → False := by
    intro a ha b hb hab
    obtain ⟨w,hw,hbw⟩ := hres b hb
    have haw : a=w := (hP.1 (hP.2 b)).unique hab.symm hbw
    rcases Finset.mem_union.mp ha with haX|haY
    · exact Finset.disjoint_left.mp hXU haX (haw ▸ hw)
    · exact Finset.disjoint_left.mp hYU haY (haw ▸ hw)
  have hpart (b : V) : b ∈ S ∨ b ∈ X ∨ b ∈ Y ∨ b ∈ U := by
    have hh : b ∈ S ∪ X ∪ Y ∪ U := by rw [hcover]; exact Finset.mem_univ b
    simpa only [Finset.mem_union,or_assoc] using hh
  have hclosedX : ∀ a ∈ X, ∀ b, P.Adj a b → b ∉ X → a=u ∧ b=v := by
    intro a ha b hab hbX
    rcases hpart b with hbS|hbX'|hbY|hbU
    · exact False.elim (hnotS a (Finset.mem_union_left _ ha) b hbS hab)
    · exact False.elim (hbX hbX')
    · exact hcross a ha b hbY (P.adj_sub hab)
    · exact False.elim (hanti b hbU a (Finset.mem_union_left _ ha) (P.adj_sub hab).symm)
  have hclosedY : ∀ a ∈ Y, ∀ b, P.Adj a b → b ∉ Y → a=v ∧ b=u := by
    intro a ha b hab hbY
    rcases hpart b with hbS|hbX|hbY'|hbU
    · exact False.elim (hnotS a (Finset.mem_union_right _ ha) b hbS hab)
    · have hh := hcross b hbX a ha (P.adj_sub hab).symm
      exact ⟨hh.2,hh.1⟩
    · exact False.elim (hbY hbY')
    · exact False.elim (hanti b hbU a (Finset.mem_union_right _ ha) (P.adj_sub hab).symm)
  have hnotvX : v ∉ X := fun h => Finset.disjoint_left.mp hXY h hvY
  have hnotuY : u ∉ Y := fun h => Finset.disjoint_left.mp hXY huX h
  have hoddX := in1158_single_exit_local G P hP X u v huX hnotvX hPuv hclosedX
  have hoddY := in1158_single_exit_local G P hP Y v u hvY hnotuY hPuv.symm hclosedY
  exact ⟨S,X,Y,U,hSne,hSX,hSY,hSU,hXY,hXU,hYU,hcover,huX,hvY,hcross,hanti,hoddU,hoddX,hoddY⟩
