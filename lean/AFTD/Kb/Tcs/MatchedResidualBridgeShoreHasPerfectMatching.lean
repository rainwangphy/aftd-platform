import AFTD.Prelude

/-!
# matched_residual_bridge_shore_has_perfect_matching

Topic: graphs   Node: 8f68d3da0675

Provenance: helper lemma. OP-1957 uniform bridge-shore assembly.

A nonendpoint shore of a matched bridge inherits a perfect matching.
-/

theorem matched_residual_bridge_shore_has_perfect_matching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R Q W : Finset V) (x z : V) (hx : x ∈ R) (hz : z ∈ R)
    (P : (G.induce {a | a ∈ R}).Subgraph) (hP : P.IsPerfectMatching)
    (hxz : P.Adj ⟨x,hx⟩ ⟨z,hz⟩) (hpart : Q ∪ W ∪ {x,z} = R)
    (hxW : x ∉ W) (hzW : z ∉ W)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w) :
    ∃ M : (G.induce {a | a ∈ W}).Subgraph, M.IsPerfectMatching := by
  classical
  have hWR : W ⊆ R := by
    intro a ha
    rw [← hpart]
    exact Finset.mem_union_left _ (Finset.mem_union_right Q ha)
  let e : {a : V // a ∈ W} → {a : V // a ∈ R} := fun a => ⟨a.val,hWR a.property⟩
  let M : (G.induce {a | a ∈ W}).Subgraph := {
    verts := Set.univ
    Adj := fun a b => P.Adj (e a) (e b)
    adj_sub := by intro a b h; exact P.adj_sub h
    edge_vert := by intro a b h; exact Set.mem_univ a
    symm := ⟨by intro a b h; exact h.symm⟩ }
  refine ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro a
  obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 (e a))
  have hbx : b.val ≠ x := by
    intro h
    have he : b = (⟨x,hx⟩ : {a : V // a ∈ R}) := Subtype.ext h
    have hab' : P.Adj (e a) ⟨x,hx⟩ := by rwa [← he]
    have hz_a := hP.1.eq_of_adj_left hxz hab'.symm
    have hza : z = a.val := congrArg Subtype.val hz_a
    exact hzW (hza ▸ a.property)
  have hbz : b.val ≠ z := by
    intro h
    have he : b = (⟨z,hz⟩ : {a : V // a ∈ R}) := Subtype.ext h
    have hab' : P.Adj (e a) ⟨z,hz⟩ := by rwa [← he]
    have hx_a := hP.1.eq_of_adj_right hxz hab'
    have hxa : x = a.val := congrArg Subtype.val hx_a
    exact hxW (hxa ▸ a.property)
  have hbW : b.val ∈ W := by
    have hb : b.val ∈ Q ∪ W ∪ {x,z} := by rw [hpart]; exact b.property
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with (hb | hb) | hb | hb
    · exact (hcross b.val hb a.val a.property (P.adj_sub hab.symm)).elim
    · exact hb
    · exact (hbx hb).elim
    · exact (hbz hb).elim
  refine ⟨⟨b.val,hbW⟩, ?_, ?_⟩
  · change P.Adj (e a) (e ⟨b.val,hbW⟩)
    have he : e ⟨b.val,hbW⟩ = b := Subtype.ext rfl
    rwa [he]
  · intro c hc
    apply Subtype.ext
    have he : e c = b := huniq (e c) hc
    exact (show c.val = b.val from congrArg (fun t : {a : V // a ∈ R} => t.val) he)
