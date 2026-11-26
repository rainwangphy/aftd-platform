import AFTD.Prelude

/-!
# odd_groups_budget_after_forced_matching

Topic: graphs   Node: 409d15f70969

Provenance: helper lemma. Matching and odd-component budget for OP-1957; https://arxiv.org/abs/2611.22690.

Odd anticomplete groups disjoint from a forced matching require distinct matching partners outside the groups and outside the forced matching.
-/

theorem odd_groups_budget_after_forced_matching
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (P T : G.Subgraph) [DecidablePred (fun v => v ∈ T.verts)]
    (hP : P.IsPerfectMatching) (hT : T.IsMatching) (hTP : T ≤ P)
    (J : Finset I) (F : I → Finset V) (L : Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ L) (hodd : ∀ i ∈ J, Odd (F i).card)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ G.Adj u v)
    (hfree : ∀ i ∈ J, ∀ u ∈ F i, u ∉ T.verts) :
    J.card ≤ ((Finset.univ \ L).filter (fun v => v ∉ T.verts)).card := by
  classical
  have hkey : ∀ i ∈ J, ∃ b : V, b ∉ L ∧ b ∉ T.verts ∧ ∃ a ∈ F i, P.Adj a b := by
    intro i hi
    have hout : ∃ b : V, b ∉ L ∧ ∃ a ∈ F i, P.Adj a b := by
      by_contra hno
      push Not at hno
      let C : Set V := (F i : Set V)
      have hmatch : (P.induce C).IsMatching := by
        intro a ha
        have haF : a ∈ F i := ha
        obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
        have hbL : b ∈ L := by
          by_contra hb
          exact hno b hb a haF hab
        have hbF : b ∈ F i := by
          by_contra hb
          exact hanti i hi a haF b hbL hb (P.adj_sub hab)
        refine ⟨b,⟨haF,hbF,hab⟩,?_⟩
        intro z hz
        exact huniq z hz.2.2
      have hfin : Fintype (P.induce C).verts := Fintype.ofFinite _
      have he := hmatch.even_card
      rw [← Set.ncard_eq_toFinset_card'] at he
      have hC : (P.induce C).verts.ncard = (F i).card := by
        show C.ncard = _
        simp [C]
      rw [hC] at he
      exact (Nat.not_even_iff_odd.mpr (hodd i hi)) he
    obtain ⟨b,hb,a,ha,hab⟩ := hout
    refine ⟨b,hb,?_,a,ha,hab⟩
    intro hbT
    obtain ⟨z,hbz,_⟩ := hT hbT
    have hpz : P.Adj b z := hTP.2 hbz
    have hza : z = a := (hP.1 (hP.2 b)).unique hpz hab.symm
    apply hfree i hi a ha
    rw [← hza]
    exact hbz.snd_mem
  let f : J → {v : V // v ∈ (Finset.univ \ L).filter (fun w => w ∉ T.verts)} := fun i =>
    ⟨(hkey i.val i.property).choose, by
      have hh := (hkey i.val i.property).choose_spec
      simp [hh.1,hh.2.1]⟩
  have hinj : Function.Injective f := by
    intro i j heq
    obtain ⟨_,_,ai,hai,hPi⟩ := (hkey i.val i.property).choose_spec
    obtain ⟨_,_,aj,haj,hPj⟩ := (hkey j.val j.property).choose_spec
    have he : (hkey i.val i.property).choose = (hkey j.val j.property).choose := congrArg Subtype.val heq
    rw [he] at hPi
    have hb : (hkey j.val j.property).choose ∈ P.verts := P.edge_vert hPi.symm
    have ha : ai=aj := (hP.1 hb).unique hPi.symm hPj.symm
    apply Subtype.ext
    by_contra hij
    have hd := hdis i.val i.property j.val j.property hij
    exact Finset.disjoint_left.mp hd hai (ha ▸ haj)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc
