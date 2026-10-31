import AFTD.Prelude

/-!
# simple_graph_radius_ne_top_of_connected

Topic: graphs   Node: ae548b3b97cb

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

The radius of any finite connected simple graph is finite (not top in WithTop Nat).
-/

/-- The radius of a finite connected simple graph is finite. -/
theorem simple_graph_radius_ne_top_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V) (hconn : G.Connected) : G.radius ≠ ⊤ := by
  haveI := hconn.nonempty
  exact SimpleGraph.radius_ne_top_iff.mpr hconn
