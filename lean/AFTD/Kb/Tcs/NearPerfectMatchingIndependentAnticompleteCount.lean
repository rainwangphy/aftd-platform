import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# near_perfect_matching_independent_anticomplete_count

Topic: graphs   Node: 2e978d7a0d5e

Provenance: helper lemma. Positive-separator transfer for OP-1957; https://arxiv.org/abs/2611.22690.

If a matching misses at most two vertices of R, an independent subset U and a disjoint anticomplete subset W obey 2|U|+|W|≤|R|+2.
-/

theorem near_perfect_matching_independent_anticomplete_count
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (R U W : Finset V) (M : G.Subgraph) (hM : M.IsMatching)
    (hMR : M.verts ⊆ (R : Set V)) (hnear : R.card ≤ 2*M.edgeSet.ncard+2)
    (hUR : U ⊆ R) (hWR : W ⊆ R) (hdis : Disjoint U W)
    (hUind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (hanti : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w) :
    2*U.card+W.card ≤ R.card+2 := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset V := M.verts.toFinset
    let Q : Finset V := U ∩ D
    let Z : Finset V := R \ (U ∪ W)
    have hDR : D ⊆ R := by intro x hx; exact hMR (by simpa [D] using hx)
    have hDcard : D.card = 2*M.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hM).symm
    have hQZ : Q.card ≤ Z.card := by
      let f : {x // x ∈ Q} → {y // y ∈ Z} := fun x =>
        let hxU : x.val ∈ U := (Finset.mem_inter.mp x.property).1
        let hxM : x.val ∈ M.verts := by
          have hxD := (Finset.mem_inter.mp x.property).2
          simpa [D] using hxD
        let y := Classical.choose (hM hxM)
        let hxy := (Classical.choose_spec (hM hxM)).1
        ⟨y,Finset.mem_sdiff.mpr ⟨hMR (M.edge_vert hxy.symm),by
          intro hy
          rcases Finset.mem_union.mp hy with hyU | hyW
          · exact hUind x.val hxU y hyU (M.adj_sub hxy)
          · exact hanti x.val hxU y hyW (M.adj_sub hxy)⟩⟩
      have hinj : Function.Injective f := by
        intro a b hab
        let haM : a.val ∈ M.verts := by
          have ha := (Finset.mem_inter.mp a.property).2
          simpa [D] using ha
        let hbM : b.val ∈ M.verts := by
          have hb := (Finset.mem_inter.mp b.property).2
          simpa [D] using hb
        let ya := Classical.choose (hM haM)
        let yb := Classical.choose (hM hbM)
        have he : ya=yb := by
          have hh := congrArg Subtype.val hab
          change ya = yb at hh
          exact hh
        have hay : M.Adj ya a.val := (Classical.choose_spec (hM haM)).1.symm
        have hby : M.Adj ya b.val := by rw [he]; exact (Classical.choose_spec (hM hbM)).1.symm
        have hya : ya ∈ M.verts := M.edge_vert hay
        apply Subtype.ext
        exact (hM hya).unique hay hby
      have hh := Fintype.card_le_of_injective f hinj
      simpa using hh
    have hUQ : U.card ≤ Q.card+2 := by
      have hsub : U \ D ⊆ R \ D := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hUR (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
      have hc := Finset.card_le_card hsub
      have hRD := Finset.card_sdiff_add_card_eq_card hDR
      have hUD := Finset.card_sdiff_add_card_inter U D
      dsimp [Q] at hQZ ⊢
      omega
    have hUW : U ∪ W ⊆ R := Finset.union_subset hUR hWR
    have hZcard : Z.card+U.card+W.card=R.card := by
      have hh := Finset.card_sdiff_add_card_eq_card hUW
      have hc := Finset.card_union_of_disjoint hdis
      dsimp [Z]
      omega
    omega
