import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalTwinsForcedEdgeIsBridge
import AFTD.Kb.Tcs.FactorcriticalFalseTwinsForcedResidualEdgeIsBridge
import AFTD.Kb.Tcs.FactorcriticalInduceOneAfterVertexRestriction
import AFTD.Kb.Tcs.PerfectMatchingTransportGraphIso

/-!
# factorcritical_twins_forced_residual_edge_is_bridge

Topic: graphs   Node: cbd069b570c0

Provenance: helper lemma. OP-1957; unrestricted factor-critical twin bridge route, extending the proved false-twin residual lemma.

In a 2k-factor-critical graph, a forced residual matching edge incident to one of two vertices with identical neighborhoods outside the pair is a bridge when the other twin lies outside the residual, whether the twins are adjacent or not.
-/

theorem factorcritical_twins_forced_residual_edge_is_bridge (k n : ℕ) (G : SimpleGraph (Fin n)) (hcrit : is_k_factor_critical G (2*k)) (R : Finset (Fin n)) (hR : R.card + 2*k = n) (x y z : Fin n) (hxy : x ≠ y) (htwin : ∀ a, a ≠ x → a ≠ y → (G.Adj x a ↔ G.Adj y a)) (hx : x ∈ R) (hz : z ∈ R) (hy : y ∉ R) (hxz : G.Adj x z) (hforced : ¬ ∃ P : ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching) : ¬ ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hx⟩,⟨z,hz⟩)}).Reachable ⟨x,hx⟩ ⟨z,hz⟩ := by
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
  have htwin' : ∀ a, a ≠ x' → a ≠ y' → (D.Adj x' a ↔ D.Adj y' a) := by
    intro a hax hay
    change G.Adj x a.val ↔ G.Adj y a.val
    apply htwin a.val
    · intro he; apply hax; exact Subtype.ext he
    · intro he; apply hay; exact Subtype.ext he
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
  have hbridge := factorcritical_twins_forced_edge_is_bridge D hDcrit x' y' z' hxy' htwin' hzy' hxz hforcedD
  intro hreach
  apply hbridge
  have hh := hreach.map e.toHom
  change ((D.induce {a | a ≠ y'}).deleteEdges
    {s(e0 ⟨x,hx⟩,e0 ⟨z,hz⟩)}).Reachable (e0 ⟨x,hx⟩) (e0 ⟨z,hz⟩) at hh
  rw [heX, heZ] at hh
  exact hh
