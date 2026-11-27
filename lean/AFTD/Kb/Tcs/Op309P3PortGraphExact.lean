import AFTD.Prelude
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort

/-!
# op309_p3_port_graph_exact

Topic: graphs   Node: 6a1971b22c48

Provenance: helper lemma. OP-309 exact P3 port quotient, local host analysis 42558–42562.

The graph has exactly the inequalities imposed by uncovered vertices and selected P3 port triangles, with no extra edges.
-/

def op309_p3_port_graph_exact {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet)
    (Q : SimpleGraph A) (q : Sum G.edgeSet (V × Fin 3) → A) : Prop :=
  let d : V → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
  ∀ x y : A, Q.Adj x y ↔ x ≠ y ∧
    ((∃ (v : V) (e f : G.edgeSet), d v = 0 ∧
       e ∉ R ∧ f ∉ R ∧ v ∈ e.1 ∧ v ∈ f.1 ∧
       q (.inl e) = x ∧ q (.inl f) = y) ∨
     (∃ (a b c : V) (ea ea' eb : Sum G.edgeSet (V × Fin 3)),
       [a,b,c].Nodup ∧ s(a,b) ∈ R.image Subtype.val ∧
       s(b,c) ∈ R.image Subtype.val ∧ d a = 1 ∧ d b = 2 ∧ d c = 1 ∧
       op309_padded_boundary_port G R a ea ∧
       op309_padded_boundary_port G R a ea' ∧ ea ≠ ea' ∧
       op309_padded_boundary_port G R b eb ∧
       x ∈ [q ea, q ea', q eb] ∧ y ∈ [q ea, q ea', q eb]))
