import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet

/-!
# conn_set_poly

Topic: graphs   Node: d81004bb3280

Provenance: helper lemma. step towards op_599_connected_induced_activity_clique_minimum

The connected-set generating polynomial Z_G = sum over nonempty vertex sets S inducing a connected subgraph of X^{|S|}.
-/

open scoped BigOperators Polynomial Classical in
/-- Z_G(X) = Σ over connected nonempty S ⊆ V of X^|S|. -/
noncomputable def conn_set_poly {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℝ := ∑ S ∈ Finset.univ.filter (fun S : Finset V => is_connected_vertex_set G (↑S : Set V)),
    (Polynomial.X : Polynomial ℝ) ^ S.card
