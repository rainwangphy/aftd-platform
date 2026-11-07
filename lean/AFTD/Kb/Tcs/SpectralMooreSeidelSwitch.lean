import AFTD.Prelude

/-!
# spectral_moore_seidel_switch

Topic: graphs   Node: 98885bf117e1

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Section 5, Seidel switching

Seidel switching: for a simple graph G : SimpleGraph V and a set X : Set V, the simple graph on V in which distinct vertices u, v are adjacent iff (G.Adj u v ↔ (u ∈ X ↔ v ∈ X)); that is, edges and non-edges are kept inside X and inside its complement and interchanged between X and its complement.
-/

/-- Seidel switching of `G` with respect to the vertex set `X`. -/
def spectral_moore_seidel_switch {V : Type*} (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ↔ (u ∈ X ↔ v ∈ X))
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by rw [G.adj_comm]; exact h.2.trans (by tauto)⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl
