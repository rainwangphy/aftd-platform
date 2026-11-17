import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFaceSumReal

/-!
# simple_graph_has_list_facial_distinguishing_labeling

Topic: combinatorics   Node: c419020e0db7

Provenance: formalization of a published result. Source: arXiv:2611.18384 Definition 2.1

A graph G with rotation system σ admits an adjacent-facial-sum-distinguishing proper vertex labeling from arbitrary real lists of size k + 1 if for every assignment of real lists A(v) of cardinality k + 1, there exists a proper vertex labeling c with c(v) ∈ A(v) distinguishing edge-adjacent facial sums.
-/

/-- Predicate that G admits a facial-sum-distinguishing proper vertex labeling from any real lists of size k + 1. -/
def simple_graph_has_list_facial_distinguishing_labeling {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) (k : ℕ) : Prop :=
  ∀ A : Fin n → Finset ℝ, (∀ v, (A v).card = k + 1) →
    ∃ c : Fin n → ℝ, (∀ v, c v ∈ A v) ∧
      (∀ u v, G.Adj u v → c u ≠ c v) ∧
      ∀ d : G.Dart, simple_graph_face_sum_real G σ c d ≠ simple_graph_face_sum_real G σ c d.symm
