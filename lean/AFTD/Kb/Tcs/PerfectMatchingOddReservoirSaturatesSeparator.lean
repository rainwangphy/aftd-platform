import AFTD.Prelude

/-!
# perfect_matching_odd_reservoir_saturates_separator

Topic: graphs   Node: 66d67fd0b0fa

Provenance: helper lemma. OP-1957, forced-edge barrier endpoint parity

If U has at least as many odd components as a disjoint separator S, U is anticomplete outside U∪S, and P is a perfect matching, then every vertex of S is matched into U.
-/

set_option maxHeartbeats 3000000

theorem perfect_matching_odd_reservoir_saturates_separator {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (P : G.Subgraph) (hP : P.IsPerfectMatching) (S U : Finset V) (hSU : Disjoint S U) (hanti : ∀ u ∈ U, ∀ v, v ∉ U → v ∉ S → ¬ G.Adj u v) (hodd : S.card ≤ (G.induce {v | v ∈ U}).oddComponents.ncard) : ∀ s ∈ S, ∃ u ∈ U, P.Adj s u := by
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
