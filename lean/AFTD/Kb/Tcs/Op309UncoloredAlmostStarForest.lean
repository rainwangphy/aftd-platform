import AFTD.Prelude

/-!
# op309_uncolored_almost_star_forest

Topic: graphs   Node: 8ef0c1361dcd

Provenance: helper lemma. Structural part of the OP-309 almost-star route.

A selected edge set whose nonempty components are trees with two or three edges.
-/

def op309_uncolored_almost_star_forest {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset G.edgeSet) : Prop :=
    (∀ e ∈ R, ∃ f ∈ R, G.lineGraph.Adj e f) ∧
    (∀ a b d : V, [a,b,d].Nodup →
      ¬ (s(a,b) ∈ R.image Subtype.val ∧ s(b,d) ∈ R.image Subtype.val ∧
         s(d,a) ∈ R.image Subtype.val)) ∧
    (∀ e₀ ∈ R, ∀ e₁ ∈ R, ∀ e₂ ∈ R, ∀ e₃ ∈ R,
      [e₀,e₁,e₂,e₃].Nodup →
      ¬ (G.lineGraph.Adj e₀ e₁ ∧
        (G.lineGraph.Adj e₂ e₀ ∨ G.lineGraph.Adj e₂ e₁) ∧
        (G.lineGraph.Adj e₃ e₀ ∨ G.lineGraph.Adj e₃ e₁ ∨ G.lineGraph.Adj e₃ e₂)))
