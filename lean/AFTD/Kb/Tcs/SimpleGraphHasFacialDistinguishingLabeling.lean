import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFaceSum

/-!
# simple_graph_has_facial_distinguishing_labeling

Topic: combinatorics   Node: 200851457796

Provenance: formalization of a published result. Source: arXiv:2611.18384 Def. 2.1

A simple graph G on Fin n with decidable adjacency and dart permutation σ admits an adjacent-facial-sum-distinguishing proper vertex labeling with bound k if there exists a coloring c : Fin n → Fin (k + 1) such that c u ≠ c v whenever G.Adj u v, and for every dart d of G, simple_graph_face_sum G σ (fun v => (c v : ℕ)) d ≠ simple_graph_face_sum G σ (fun v => (c v : ℕ)) d.symm.
-/

/-- Predicate that G admits an adjacent-facial-sum-distinguishing proper vertex labeling with labels in {0, ..., k}. -/
def simple_graph_has_facial_distinguishing_labeling {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin (k + 1),
    (∀ u v, G.Adj u v → c u ≠ c v) ∧
    ∀ d : G.Dart, simple_graph_face_sum G σ (fun v => (c v : ℕ)) d ≠
      simple_graph_face_sum G σ (fun v => (c v : ℕ)) d.symm
