import AFTD.Prelude

/-!
# simple_graph_coloring_is_achromatic

Topic: graphs   Node: 80d66b0ea524

Provenance: formalization of a published result. Source: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs), Sec. 1, definition of an achromatic colouring

A proper vertex colouring with k colours is achromatic if all k colours are used and there is at least one edge between each pair of distinct colour classes.
-/

/-- A proper colouring with colours `Fin k` is achromatic (complete) if every colour is used and every two distinct colour classes are joined by an edge. -/
def simple_graph_coloring_is_achromatic {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (C : G.Coloring (Fin k)) : Prop :=
  Function.Surjective C ∧ ∀ i j : Fin k, i ≠ j → ∃ u v, G.Adj u v ∧ C u = i ∧ C v = j
