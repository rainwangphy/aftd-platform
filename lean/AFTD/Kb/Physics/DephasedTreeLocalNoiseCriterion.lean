import AFTD.Prelude

/-!
# dephased_tree_local_noise_criterion

Topic: quantum_mechanics   Node: b87ab119f329

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V and noise profile q : V → ℝ, dephased_tree_local_noise_criterion T q holds if both local conditions hold: (i) at every degree-two vertex v with distinct neighbors u and w, q v ≥ q u * q w; (ii) at every vertex v of degree at least three, at most one neighbor u has q u > 0 (that is, any two neighbors u and w with q u > 0 and q w > 0 must be equal).
-/

/-- Local noise criterion for MMI on an inhomogeneously dephased tree. -/
def dephased_tree_local_noise_criterion {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) : Prop := (∀ (v : V), T.degree v = 2 →
    ∀ (u w : V), u ≠ w → T.Adj v u → T.Adj v w → q v ≥ q u * q w) ∧
  (∀ (v : V), 3 ≤ T.degree v →
    ∀ (u w : V), T.Adj v u → T.Adj v w → 0 < q u → 0 < q w → u = w)
