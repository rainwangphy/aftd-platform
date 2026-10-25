import AFTD.Prelude

/-!
# simple_graph_has_modulo_orientation

Topic: graphs   Node: be902ab7cc11

Provenance: formalization of a published result. Source: arXiv:2610.07034 Sec. 1, p. 3

A simple graph G on a finite vertex set V has a modulo-q orientation if there exists an orientation directing each edge such that for every vertex v, its outdegree is congruent to its indegree modulo q.
-/

/-- A simple graph has a modulo-q orientation if there exists an orientation directing each edge such that at every vertex the outdegree is congruent to the indegree modulo q. -/
def simple_graph_has_modulo_orientation {V : Type*} [Fintype V] (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∃ R : V → V → Prop,
    ((∀ u v, R u v → G.Adj u v) ∧
     (∀ u v, G.Adj u v → (R u v ∧ ¬ R v u ∨ R v u ∧ ¬ R u v))) ∧
    ∀ v : V,
      (open Classical in ((Finset.univ.filter (fun w => R v w)).card : ZMod q)) =
      (open Classical in ((Finset.univ.filter (fun w => R w v)).card : ZMod q))
