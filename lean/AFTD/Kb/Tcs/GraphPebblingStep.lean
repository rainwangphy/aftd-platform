import AFTD.Prelude

/-!
# graph_pebbling_step

Topic: graphs   Node: 7b56d59f0be9

Provenance: formalization of a published result. Source: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Sec. 2 (pebbling step u ⇒ v).

A pebbling step on a graph G turns the configuration c : V → ℕ into c' when some edge uv has c(u) ≥ 2 and c' is c with two pebbles removed from u and one added at v.
-/

/-- One pebbling step `c ⟶ c'` on `G`: along some edge `uv` with `c u ≥ 2`, remove two pebbles from `u` and add one to `v`. -/
def graph_pebbling_step {V : Type*} [DecidableEq V] (G : SimpleGraph V) (c c' : V → ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ c u ∧ c' = Function.update (Function.update c u (c u - 2)) v (c v + 1)
