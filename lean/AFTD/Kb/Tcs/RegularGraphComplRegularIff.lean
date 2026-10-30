import AFTD.Prelude

/-!
# regular_graph_compl_regular_iff

Topic: graphs   Node: 6e98ed14344e

Provenance: helper lemma. step towards regular_graph_lap_trace_minimal_iff_compl_adj_trace_minimal

Let G be a simple graph on a finite vertex set V with cardinality n. If d + 1 ≤ n, then G is d-regular if and only if its complement Gᶜ is (n - 1 - d)-regular.
-/

open scoped Classical in
/-- A simple graph G on n vertices is d-regular if and only if its complement Gᶜ is (n - 1 - d)-regular. -/
theorem regular_graph_compl_regular_iff
    {V : Type*} [Fintype V] (d : ℕ) (hn : d + 1 ≤ Fintype.card V) (G : SimpleGraph V) :
    G.IsRegularOfDegree d ↔ Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - d) := by
  constructor
  · intro h
    exact h.compl
  · intro h v
    have hv := h v
    rw [SimpleGraph.degree_compl] at hv
    have hdeg := SimpleGraph.degree_lt_card_verts (G := G) v
    omega
