import AFTD.Prelude
import AFTD.Kb.Tcs.IsPerronVector

/-!
# is_principal_vertex

Topic: graphs   Node: a3dcb4f372a5

Provenance: formalization of a published result. Source: arXiv:2610.17078, Section 2

For a simple graph G on a finite vertex type V, a vertex u is a principal vertex if there exists a Perron vector vec of G such that vec v ≤ vec u for all vertices v.
-/

/-- A principal vertex of a simple graph is a vertex where some Perron vector achieves its maximum coordinate. -/
def is_principal_vertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u : V) : Prop := ∃ vec, is_perron_vector G vec ∧ ∀ v, vec v ≤ vec u
