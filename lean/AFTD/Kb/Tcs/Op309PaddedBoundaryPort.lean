import AFTD.Prelude

/-!
# op309_padded_boundary_port

Topic: graphs   Node: 73f60e1805eb

Provenance: helper lemma. Private dummy-port construction for the OP-309 almost-star route.

An outside original edge incident to v or one of the private dummy ports padding v to cubic degree.
-/

def op309_padded_boundary_port {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet)
    (v : V) (p : Sum G.edgeSet (V × Fin 3)) : Prop :=
    match p with
    | .inl e => e ∉ R ∧ v ∈ e.1
    | .inr (w,j) => w = v ∧ j.val < 3 - G.degree v
