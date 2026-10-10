import AFTD.Prelude

/-!
# graph_wasserstein_dist

Topic: graphs   Node: e1107b84622d

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Definition 2.1 (Wasserstein distance); finite vertex set, plans written as nonnegative functions V → V → ℝ (for probability measures they take values in [0,1] as in the paper).

The Wasserstein distance W(μ, ν) between two measures on the vertices of a finite graph: the infimum, over all transport plans π ≥ 0 with row sums μ and column sums ν, of the cost Σ_{a,b} d(a,b) π(a,b), d the graph distance.
-/

/-- Wasserstein (earth mover's) distance between `μ` and `ν` on a finite graph, with the graph distance as cost. -/
noncomputable def graph_wasserstein_dist {V : Type*} [Fintype V] (G : SimpleGraph V)
    (μ ν : V → ℝ) : ℝ :=
  sInf {c | ∃ π : V → V → ℝ, (∀ a b, 0 ≤ π a b) ∧ (∀ a, ∑ b, π a b = μ a) ∧
    (∀ b, ∑ a, π a b = ν b) ∧ c = ∑ a, ∑ b, (G.dist a b : ℝ) * π a b}
