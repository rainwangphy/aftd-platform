import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_rich_almost_star_forest

Topic: graphs   Node: 07cad2def206

Provenance: helper lemma. Selected-rich version of the known almost-star forest route for OP-309.

A set of rich edges whose components have two or three edges and are trees; in a subcubic graph the components are two-edge paths, three-edge stars, and three-edge paths.
-/

def op309_rich_almost_star_forest {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5))
    (R : Finset G.edgeSet) : Prop :=
    (∀ e ∈ R, simple_graph_edge_is_rich G c e) ∧
    (∀ e ∈ R, ∃ f ∈ R, G.lineGraph.Adj e f) ∧
    (∀ a b d : V, [a,b,d].Nodup →
      ¬ (s(a,b) ∈ R.image Subtype.val ∧ s(b,d) ∈ R.image Subtype.val ∧
         s(d,a) ∈ R.image Subtype.val)) ∧
    (∀ e₀ ∈ R, ∀ e₁ ∈ R, ∀ e₂ ∈ R, ∀ e₃ ∈ R,
      [e₀,e₁,e₂,e₃].Nodup →
      ¬ (G.lineGraph.Adj e₀ e₁ ∧
        (G.lineGraph.Adj e₂ e₀ ∨ G.lineGraph.Adj e₂ e₁) ∧
        (G.lineGraph.Adj e₃ e₀ ∨ G.lineGraph.Adj e₃ e₁ ∨ G.lineGraph.Adj e₃ e₂)))
