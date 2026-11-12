import AFTD.Prelude

/-!
# is_half_integral_current

Topic: statistical_mechanics   Node: 72c8d2fcfe5d

Provenance: formalization of a published result. Source: arXiv:2204.00875

For a finite simple graph G with decidable equality on vertices and decidable adjacency, a function j on the edge finset of G into the reals is half-integral if for every edge e in G.edgeFinset, j(e) is equal to 0, 1/2, -1/2, 1, or -1.
-/

/-- A function j on the edges of G is half-integral if every edge current lies in {0, ±1/2, ±1}. -/
def is_half_integral_current {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : G.edgeFinset → ℝ) : Prop := ∀ e : G.edgeFinset, j e = 0 ∨ j e = 1/2 ∨ j e = -1/2 ∨ j e = 1 ∨ j e = -1
