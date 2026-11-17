import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasFacialDistinguishingLabeling

/-!
# simple_graph_facial_distinguishing_param

Topic: combinatorics   Node: 121a3ef6ad3c

Provenance: formalization of a published result. Source: arXiv:2611.18384 Definition 2.1

Given a simple graph G on vertex set Fin n and a permutation σ of the darts of G (defining a rotation system / facial structure), the adjacent-facial-sum-distinguishing labeling parameter λ(G, σ) is the least non-negative integer k such that G admits an adjacent-facial-sum-distinguishing proper vertex labeling with values in {0, ..., k}.
-/

/-- The facial-sum-distinguishing labeling parameter λ(G). -/
noncomputable def simple_graph_facial_distinguishing_param {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) : ℕ :=
  sInf {k : ℕ | simple_graph_has_facial_distinguishing_labeling G σ k}
