import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCliquePolynomial

/-!
# simple_graph_q

Topic: graphs   Node: f3858a6481ab

Provenance: formalization of a published result. Source: arXiv:2611.14430, Section 4

The invariant $q(G) = C_G(-1)$ of a finite simple graph $G$, obtained by evaluating its clique polynomial at $-1$.
-/

/-- The invariant q(G) obtained by evaluating the clique polynomial at -1. -/
noncomputable def simple_graph_q {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  (simple_graph_clique_polynomial G).eval (-1)
