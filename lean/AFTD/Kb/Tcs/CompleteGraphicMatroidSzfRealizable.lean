import AFTD.Prelude
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.Tcs.CompleteGraphCycleClosure

/-!
# complete_graphic_matroid_szf_realizable

Topic: graphs   Node: 2a41ce7820fb

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 1 (SZF-realizable matroid), specialised to M(K_n)

The cycle matroid M(K_n) is SZF-realizable: there is a multigraph on the ground set E(K_n) (symmetric adjacency multiplicities μ, loops allowed) whose skew zero forcing closure equals the closure of M(K_n) on every set of edges.
-/

/-- `M(K_n)` is SZF-realizable by some multigraph on its ground set. -/
def complete_graphic_matroid_szf_realizable (n : ℕ) : Prop :=
  ∃ μ : (⊤ : SimpleGraph (Fin n)).edgeSet → (⊤ : SimpleGraph (Fin n)).edgeSet → ℕ,
    (∀ u v, μ u v = μ v u) ∧
    ∀ S, szf_multigraph_closure μ S = complete_graph_cycle_closure n S
