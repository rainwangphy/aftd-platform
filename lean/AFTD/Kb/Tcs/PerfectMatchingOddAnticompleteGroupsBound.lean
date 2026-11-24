import AFTD.Prelude

/-!
# perfect_matching_odd_anticomplete_groups_bound

Topic: graphs   Node: 4340057848e4

Provenance: helper lemma. OP-1957, graph-to-odd-group counting

In a graph with a perfect matching, disjoint odd vertex groups that are anticomplete to the rest of L cannot outnumber vertices outside L.
-/

set_option maxHeartbeats 3000000

theorem perfect_matching_odd_anticomplete_groups_bound {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I] (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (J : Finset I) (F : I → Finset V) (L : Finset V) (hsub : ∀ i ∈ J, F i ⊆ L) (hodd : ∀ i ∈ J, Odd (F i).card) (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j)) (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ G.Adj u v) : J.card ≤ ((Finset.univ : Finset V) \ L).card := by
  classical
  have hkey : ∀ i ∈ J, ∃ b : V, b ∉ L ∧ ∃ a ∈ F i, P.Adj a b := by
    intro i hi
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
  let f : J → {v : V // v ∉ L} := fun i =>
    ⟨(hkey i.val i.property).choose, (hkey i.val i.property).choose_spec.1⟩
  have hinj : Function.Injective f := by
    intro i j heq
    obtain ⟨_,ai,hai,hPi⟩ := (hkey i.val i.property).choose_spec
    obtain ⟨_,aj,haj,hPj⟩ := (hkey j.val j.property).choose_spec
    have he : (hkey i.val i.property).choose = (hkey j.val j.property).choose := congrArg Subtype.val heq
    rw [he] at hPi
    have hb : (hkey j.val j.property).choose ∈ P.verts := P.edge_vert hPi.symm
    have ha : ai=aj := (hP.1 hb).unique hPi.symm hPj.symm
    apply Subtype.ext
    by_contra hij
    have hd := hdis i.val i.property j.val j.property hij
    exact Finset.disjoint_left.mp hd hai (ha ▸ haj)
  have hcard := Fintype.card_le_of_injective f hinj
  have hc : Fintype.card {v : V // v ∉ L} = ((Finset.univ : Finset V) \ L).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  simpa [Fintype.card_coe,hc] using hcard
