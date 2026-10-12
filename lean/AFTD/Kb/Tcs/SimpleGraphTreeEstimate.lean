import AFTD.Prelude

/-!
# simple_graph_tree_estimate

Topic: graphs   Node: 0451346c1512

Provenance: formalization of a published result. Source: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 5.1 (the tree estimate). Defined for every finite graph; a leaf is a vertex of degree 1.

The tree estimate estim(T) = max{2, 1 + max_r (ρ_T(r) + leaf_T(r))}, where leaf_T(r) is the number of leaves of T other than r and ρ_T(r) = Σ deg(v)·2^{dist_T(r,v)} over the vertices v with v = r or deg(v) > 1.
-/

/-- The tree estimate `estim(T) = max 2 (1 + max_r (ρ_T(r) + leaf_T(r)))`, with `ρ_T(r) = Σ deg v · 2^dist(r,v)` over `v = r` or `deg v > 1`, and `leaf_T(r)` the number of leaves other than `r`. -/
noncomputable def simple_graph_tree_estimate {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] : ℕ :=
  max 2 (1 + Finset.univ.sup (fun r : V =>
    (∑ v ∈ Finset.univ.filter (fun v => v = r ∨ 1 < T.degree v), T.degree v * 2 ^ T.dist r v) +
      (Finset.univ.filter (fun v => v ≠ r ∧ T.degree v = 1)).card))
