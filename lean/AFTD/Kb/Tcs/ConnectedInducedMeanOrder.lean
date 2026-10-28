import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet

/-!
# connected_induced_mean_order

Topic: graphs   Node: eee3cdde1645

Provenance: formalization of a published result. Source: knowledge base, OP-599

The lambda-weighted mean order of a nonempty connected induced vertex set in a graph G is lambda * Z'_G(lambda) / Z_G(lambda), where Z_G(lambda) is the generating polynomial of connected induced vertex sets.
-/

open scoped BigOperators Polynomial in
/-- The lambda-weighted mean order of a nonempty connected induced vertex set in a graph G. -/
noncomputable def connected_induced_mean_order {V : Type*} [Fintype V] (G : SimpleGraph V) (lam : ℝ) : ℝ :=
  let Z := open scoped Classical in
    ∑ S ∈ (Finset.univ.filter (fun (S : Finset V) => is_connected_vertex_set G (↑S : Set V))),
      (Polynomial.X : Polynomial ℝ) ^ Finset.card S
  lam * (Polynomial.derivative Z).eval lam / Z.eval lam
