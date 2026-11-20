import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalFalseTwinsForcedEdgeIsBridge
import AFTD.Kb.Tcs.PerfectMatchingTransportGraphIso
import AFTD.Kb.Tcs.FactorcriticalInduceOneAfterVertexRestriction
import AFTD.Kb.Tcs.G

/-!
# factorcritical_false_twins_forced_residual_edge_is_bridge

Topic: graphs   Node: 92fec217b70e

Provenance: helper lemma. OP-1957 unrestricted bridge reduction through one-vertex factor-criticality.

In a 2k-factor-critical graph, if a residual matching edge at x is forced and the false twin y of x lies outside the residual, then that edge is a bridge of the residual, with no codegree restriction.
-/

noncomputable def in1088_iso_delete_edge {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (u v : V) :
    (G.deleteEdges {s(u,v)}) ≃g (H.deleteEdges {s(e u,e v)}) where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_rel_iff' := by
    intro a b
    change (H.deleteEdges {s(e u,e v)}).Adj (e a) (e b) ↔
      (G.deleteEdges {s(u,v)}).Adj a b
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff,
      e.map_rel_iff, e.injective.eq_iff]

noncomputable def in1088_induce_insert_delete_iso {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (y : V) (hy : y ∉ R) :
    (G.induce {a | a ∈ R}) ≃g
      ((G.induce {a | a ∈ insert y R}).induce {a | a ≠ ⟨y, by simp⟩}) where
  toFun a := ⟨⟨a.val, by simp [a.property]⟩, by
    intro h
    have ha : a.val = y := congrArg Subtype.val h
    exact hy (ha ▸ a.property)⟩
  invFun a := ⟨a.val.val, by
    have h : a.val.val = y ∨ a.val.val ∈ R := by simpa using a.val.property
    rcases h with h | h
    · exact (a.property (Subtype.ext h)).elim
    · exact h⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  map_rel_iff' := by intro a b; rfl

theorem factorcritical_false_twins_forced_residual_edge_is_bridge (k n : ℕ) (G : SimpleGraph (Fin n)) (hcrit : is_k_factor_critical G (2*k)) (R : Finset (Fin n)) (hR : R.card + 2*k = n) (x y z : Fin n) (hxy : x ≠ y) (htwin : G.neighborSet x = G.neighborSet y) (hx : x ∈ R) (hz : z ∈ R) (hy : y ∉ R) (hxz : G.Adj x z) (hforced : ¬ ∃ P : ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching) : ¬ ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hx⟩,⟨z,hz⟩)}).Reachable ⟨x,hx⟩ ⟨z,hz⟩ := by
  classical
  let S := insert y R
  let D := G.induce {a | a ∈ S}
  let x' : {a : Fin n // a ∈ S} := ⟨x, by simp [S,hx]⟩
  let y' : {a : Fin n // a ∈ S} := ⟨y, by simp [S]⟩
  let z' : {a : Fin n // a ∈ S} := ⟨z, by simp [S,hz]⟩
  have hS : S.card + 2*k = Fintype.card (Fin n) + 1 := by
    simp [S, hy]
    omega
  have hDcrit : is_k_factor_critical D 1 := factorcritical_induce_one_after_vertex_restriction G (2*k) hcrit S hS
  have hxy' : x' ≠ y' := by intro h; exact hxy (congrArg Subtype.val h)
  have hzy : z ≠ y := by intro h; exact hy (h ▸ hz)
  have hzy' : z' ≠ y' := by intro h; exact hzy (congrArg Subtype.val h)
  have htwin' : D.neighborSet x' = D.neighborSet y' := by
    ext a
    change G.Adj x a.val ↔ G.Adj y a.val
    exact Set.ext_iff.mp htwin a.val
  let e0 := in1088_induce_insert_delete_iso G R y hy
  have heX : e0 ⟨x,hx⟩ = (⟨x',hxy'⟩ : {a : {a : Fin n // a ∈ S} // a ≠ y'}) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have heZ : e0 ⟨z,hz⟩ = (⟨z',hzy'⟩ : {a : {a : Fin n // a ∈ S} // a ≠ y'}) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let e := in1088_iso_delete_edge _ _ e0 ⟨x,hx⟩ ⟨z,hz⟩
  have hforcedD : ¬ ∃ P : ((D.induce {a | a ≠ y'}).deleteEdges
      {s(⟨x',hxy'⟩,⟨z',hzy'⟩)}).Subgraph, P.IsPerfectMatching := by
    intro h
    apply hforced
    apply perfect_matching_transport_graph_iso _ _ e.symm
    change ∃ P : ((D.induce {a | a ≠ y'}).deleteEdges
      {s(e0 ⟨x,hx⟩,e0 ⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching
    rw [heX, heZ]
    exact h
  have hbridge := factorcritical_false_twins_forced_edge_is_bridge D hDcrit x' y' z' hxy' htwin' hzy' hxz hforcedD
  intro hreach
  apply hbridge
  have hh := hreach.map e.toHom
  change ((D.induce {a | a ≠ y'}).deleteEdges
    {s(e0 ⟨x,hx⟩,e0 ⟨z,hz⟩)}).Reachable (e0 ⟨x,hx⟩) (e0 ⟨z,hz⟩) at hh
  rw [heX, heZ] at hh
  exact hh
