import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeUnextendibleMatching
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.MinimallyKExtendableHighDegreeZeroCodegreeComplementFourCycle
import AFTD.Kb.Tcs.Order

/-!
# k_extendable_essential_edge_has_forced_matching_residual

Topic: graphs   Node: fe5fb8e27394

Provenance: helper lemma. OP-1957 transfer from essentiality to the saturated-twin bridge residual.

An essential edge of a k-extendible graph is forced in a perfect-matching residual on n−2k vertices.
-/

theorem k_extendable_essential_edge_has_forced_matching_residual (n k : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : G.Adj u v) (hext : is_k_extendable G k) (hessential : ¬ is_k_extendable (G.deleteEdges {s(u,v)}) k) : ∃ R : Finset (Fin n), R.card + 2*k = n ∧ ∃ (hu : u ∈ R) (hv : v ∈ R), (∃ P : (G.induce {a | a ∈ R}).Subgraph, P.IsPerfectMatching) ∧ ¬ ∃ P : ((G.induce {a | a ∈ R}).deleteEdges {s(⟨u,hu⟩,⟨v,hv⟩)}).Subgraph, P.IsPerfectMatching := by
  classical
  have hG' : ∀ x y : Fin n, (G.deleteEdges {s(u,v)}).Adj x y ↔ G.Adj x y ∧ s(x,y) ≠ s(u,v) := by
    intro x y
    simp [SimpleGraph.deleteEdges_adj]
  obtain ⟨M,hM,hMk,hMno⟩ := k_extendable_essential_edge_unextendible_matching G k hext s(u,v) (by simpa using huv) hessential
  have hext' := hext.2.2
  have hup : ∀ {x y : Fin n}, M.Adj x y → G.Adj x y := fun h => ((hG' _ _).mp (M.adj_sub h)).1
  let MG : G.Subgraph := ⟨M.verts, M.Adj, hup, M.edge_vert, M.symm⟩
  have hMG : MG.IsMatching := fun x hx => hM hx
  have hMGk : MG.edgeSet.ncard = k :=
    Eq.trans (congrArg Set.ncard (by ext e; induction e using Sym2.ind; exact Iff.rfl)) hMk
  obtain ⟨P, hP, hMP⟩ := hext' MG hMG hMGk
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hMPadj : ∀ {x y : Fin n}, M.Adj x y → P.Adj x y := fun h => hMP.2 h
  have hPuv : P.Adj u v := by
    by_contra h
    exact hMno (in1063_transport G u v M P hP hMP.1 (fun x y hxy => hMPadj hxy) h)
  have hnotin : ∀ x, (x = u ∨ x = v) → x ∉ M.verts := by
    intro x hx hxM
    obtain ⟨y, hy, -⟩ := hM hxM
    have hPy := hMPadj hy
    rcases hx with rfl | rfl
    · have : y = v := (hP' x).unique hPy hPuv
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 rfl
    · have : y = u := (hP' x).unique hPy hPuv.symm
      subst this
      exact ((hG' _ _).mp (M.adj_sub hy)).2 Sym2.eq_swap
  have huR : u ∉ M.verts := hnotin u (Or.inl rfl)
  have hvR : v ∉ M.verts := hnotin v (Or.inr rfl)
  have hcl : ∀ a b, P.Adj a b → a ∉ M.verts → b ∉ M.verts := by
    intro a b hab ha hbM
    obtain ⟨c, hc, -⟩ := hM hbM
    have : c = a := (hP' b).unique (hMPadj hc) hab.symm
    exact ha (this ▸ M.edge_vert hc.symm)
  let R : Finset (Fin n) := M.vertsᶜ.toFinset
  have hmem : ∀ a, a ∈ R ↔ a ∉ M.verts := by intro a; simp [R]
  have hset : (R : Set (Fin n)) = M.vertsᶜ := by ext a; simp [hmem]
  have hR : R.card + 2*k = n := by
    have hmcard := in1076_matching_twice_card hM
    rw [hMk] at hmcard
    have hc := Set.ncard_compl_add_ncard M.verts
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
    have hRc : R.card = M.vertsᶜ.ncard := by rw [← hset, Set.ncard_coe_finset]
    omega
  have hu : u ∈ R := (hmem u).mpr huR
  have hv : v ∈ R := (hmem v).mpr hvR
  refine ⟨R,hR,hu,hv,?_,?_⟩
  · let f : (G.induce {a | a ∈ R}) →g G :=
      ⟨Subtype.val, by intro a b h; exact h⟩
    let P' := P.comap f
    refine ⟨P', ?_⟩
    constructor
    · intro a ha
      obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a.val)
      have hbR : b ∈ R := (hmem b).mpr (hcl _ _ hab ((hmem a.val).mp a.property))
      refine ⟨⟨b,hbR⟩, ⟨P.adj_sub hab,hab⟩, ?_⟩
      intro c hc
      apply Subtype.ext
      exact huniq c.val hc.2
    · intro a
      exact hP.2 a.val
  · intro hQ
    obtain ⟨Q,hQ⟩ := hQ
    let f : ((G.induce {a | a ∈ R}).deleteEdges {s(⟨u,hu⟩,⟨v,hv⟩)}) →g
        (G.deleteEdges {s(u,v)}) := {
      toFun := Subtype.val
      map_rel' := by
        intro a b hab
        have hab' := SimpleGraph.deleteEdges_adj.mp hab
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hab'.1, ?_⟩
        intro he
        simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
        have he' : s(a,b) = s(⟨u,hu⟩,⟨v,hv⟩) := by
          apply Sym2.eq_iff.mpr
          rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
          · exact Or.inl ⟨Subtype.ext ha,Subtype.ext hb⟩
          · exact Or.inr ⟨Subtype.ext ha,Subtype.ext hb⟩
        exact hab'.2 (by simpa using he') }
    let N := Q.map f
    have hN : N.IsMatching := hQ.1.map f Subtype.val_injective
    have hNverts : N.verts = M.vertsᶜ := by
      rw [SimpleGraph.Subgraph.map_verts]
      ext a
      constructor
      · rintro ⟨b,hb,rfl⟩
        exact (hmem b.val).mp b.property
      · intro ha
        let a' : {a : Fin n // a ∈ R} := ⟨a,(hmem a).mpr ha⟩
        exact ⟨a',hQ.2 a',rfl⟩
    have hdis : Disjoint M.support N.support := by
      rw [hM.support_eq_verts, hN.support_eq_verts, hNverts]
      exact disjoint_compl_right
    have hMN : (M ⊔ N).IsMatching := hM.sup hN hdis
    have hspan : (M ⊔ N).IsSpanning := by
      intro a
      change a ∈ M.verts ∪ N.verts
      rw [hNverts]
      exact Classical.em (a ∈ M.verts)
    exact hMno ⟨M ⊔ N,⟨hMN,hspan⟩,le_sup_left⟩
