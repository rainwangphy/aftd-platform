import AFTD.Prelude

/-!
# graph_idle_transport_plan_main

Topic: graphs   Node: 9d5504d36a38

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

The main transport plan at idleness 1/2: with β = (1/2)/d_x, γ = (1/2)/d_y, π(u,v) = γ·[u=x][v=x] + ψ(u)[v=y] + γ[u=v][u∈C] + κ(u)·[v∈B]/|B|, where ψ(x) = 1/2 − β, ψ(y) = β, ψ = 0 elsewhere, and κ(u) = β − γ on {x} ∪ C and β on A, 0 elsewhere.
-/

/-- Explicit transport plan between the idleness-1/2 measures at x and at y, built from the edge partition. -/
noncomputable def graph_idle_transport_plan_main {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (A B C : Finset V) : V → V → ℝ := fun u v =>
    (if u = x ∧ v = x then (1/2)/(G.degree y : ℝ) else 0) +
    (if v = y then (if u = x then 1/2 - (1/2)/(G.degree x : ℝ)
      else if u = y then (1/2)/(G.degree x : ℝ) else 0) else 0) +
    (if u = v then (if u ∈ C then (1/2)/(G.degree y : ℝ) else 0) else 0) +
    (if v ∈ B then (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
      else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0) / (B.card : ℝ) else 0)
