import AFTD.Prelude

/-!
# graph_dismantling_class

Topic: graphs   Node: 88593ccd2403

Provenance: formalization of a published result. Source: arXiv:2611.14430 Definition 2.2

The dismantling class $\mathcal{D}_j$ for integer $j \ge -1$: $\mathcal{D}_{-1}$ is the class of non-empty cones, and for $j \ge 0$, a non-empty graph belongs to $\mathcal{D}_j$ if it can be reduced to $K_1$ by successive deletions of vertices whose open neighbourhood graph belongs to $\mathcal{D}_{j-1}$.
-/

/-- The dismantling class D_j: D_{-1} is non-empty cones, and for j >= 0, D_j graphs reduce to K_1 by deleting vertices whose open neighbourhoods belong to D_{j-1}. -/
inductive graph_dismantling_class : ℤ → (V : Type) → SimpleGraph V → Prop where
  | cone (V : Type) (G : SimpleGraph V) (h : Nonempty V ∧ ∃ apex : V, ∀ v : V, v ≠ apex → G.Adj apex v) :
      graph_dismantling_class (-1) V G
  | single (j : ℤ) (hj : 0 ≤ j) (V : Type) (G : SimpleGraph V) (h : Nonempty V ∧ Subsingleton V) :
      graph_dismantling_class j V G
  | step (j : ℤ) (hj : 0 ≤ j) (V : Type) (G : SimpleGraph V) (v : V)
      (h_elig : graph_dismantling_class (j - 1) ↑(G.neighborSet v) (G.induce (G.neighborSet v)))
      (h_rem : graph_dismantling_class j ↑{w : V | w ≠ v} (G.induce {w : V | w ≠ v})) :
      graph_dismantling_class j V G
