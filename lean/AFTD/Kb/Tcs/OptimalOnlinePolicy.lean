import AFTD.Prelude
import AFTD.Kb.Tcs.BellmanValue
import AFTD.Kb.Tcs.OnlineMatchingPolicy

/-!
# optimal_online_policy

Topic: online_algorithms   Node: 8eb33595ff6b

Provenance: formalization of a published result. Source: arXiv:2611.13571, Lemma 5.1

For a simple graph G on vertex set Fin n with decidable adjacency, optimal_online_policy G is the online matching policy that accepts an arriving edge e given observed edges H and unmatched vertices U if and only if e.toFinset ⊆ U and bellman_value G (insert e H) U ≤ 1 + bellman_value G (insert e H) (U \ e.toFinset).
-/

/-- The optimal online matching policy accepting edge e iff e is feasible and 1 + V(H+e, U \ e) ≥ V(H+e, U). -/
noncomputable def optimal_online_policy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    OnlineMatchingPolicy n :=
  fun H U e =>
    decide (e.toFinset ⊆ U ∧
      bellman_value G (insert e H) U ≤ 1 + bellman_value G (insert e H) (U \ e.toFinset))
