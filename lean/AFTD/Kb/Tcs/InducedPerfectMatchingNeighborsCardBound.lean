import AFTD.Prelude

/-!
# induced_perfect_matching_neighbors_card_bound

Topic: graphs   Node: 0be983f3a808

Provenance: helper lemma. Elementary matching injection for the OP-1957 codegree-three analysis.

If an induced vertex set has a perfect matching, then any subset whose neighbors within it all lie in C has cardinality at most |C|.
-/

theorem induced_perfect_matching_neighbors_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R T C : Finset V) (hTR : T ⊆ R)
    (hcover : ∀ t ∈ T, ∀ v ∈ R, G.Adj t v → v ∈ C)
    (hmatch : ∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching) : T.card ≤ C.card := by
  classical
  obtain ⟨P,hP⟩ := hmatch
  have hp := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  let f : {a // a ∈ T} → {b // b ∈ C} := fun a =>
    let ar : {v // v ∈ R} := ⟨a.val,hTR a.property⟩
    let mate := Classical.choose (hp ar)
    ⟨mate.val, hcover a.val a.property mate.val mate.property (P.adj_sub (Classical.choose_spec (hp ar)).1)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    let ar : {v // v ∈ R} := ⟨a.val,hTR a.property⟩
    let br : {v // v ∈ R} := ⟨b.val,hTR b.property⟩
    let am := Classical.choose (hp ar)
    let bm := Classical.choose (hp br)
    have hm : am = bm := by
      apply Subtype.ext
      have hval := congrArg (fun t : {b // b ∈ C} => t.val) hab
      change am.val = bm.val at hval
      exact hval
    have ha : P.Adj am ar := (Classical.choose_spec (hp ar)).1.symm
    have hb : P.Adj am br := by rw [hm]; exact (Classical.choose_spec (hp br)).1.symm
    have heq : ar = br := (hp am).unique ha hb
    apply Subtype.ext
    have hval := congrArg (fun t : {v // v ∈ R} => t.val) heq
    change a.val = b.val at hval
    exact hval
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc
