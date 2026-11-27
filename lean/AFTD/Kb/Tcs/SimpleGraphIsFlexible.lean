import AFTD.Prelude

/-!
# simple_graph_is_flexible

Topic: graphs   Node: 1809fbe80725

Provenance: formalization of a published result. Source: arXiv:2611.34348:171

A finite simple graph G is (k, ε)-flexible if for every k-list assignment L and every request function r on a nonempty subset V_hat of vertices, there exists a proper L-coloring of G satisfying at least ε * |V_hat| requests.
-/

open Classical Finset in
/-- A finite graph is (k, ε)-flexible if every list assignment of size k with requests on a nonempty subset admits a proper coloring satisfying at least an ε-fraction of the requests. -/
def simple_graph_is_flexible {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ (C : Type*) [DecidableEq C] (L : V → Finset C) (hL : ∀ v, (L v).card = k)
    (V_hat : Finset V) (hV : V_hat.Nonempty) (r : V → C) (hr : ∀ v ∈ V_hat, r v ∈ L v),
    ∃ f : V → C, (∀ u v, G.Adj u v → f u ≠ f v) ∧ (∀ v, f v ∈ L v) ∧
      ε * (V_hat.card : ℝ) ≤ ((V_hat.filter (fun v => f v = r v)).card : ℝ)
