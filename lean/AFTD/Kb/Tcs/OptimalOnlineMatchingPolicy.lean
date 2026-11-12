import AFTD.Prelude
import AFTD.Kb.Tcs.BellmanValue
import AFTD.Kb.Tcs.OptimalOnlinePolicy
import AFTD.Kb.Tcs.PolicyValue
import AFTD.Kb.Tcs.OptimalOnlineMatchingPolicyAchievesValue
import AFTD.Kb.Tcs.OnlineMatchingPolicyValueLeBellman
import AFTD.Kb.Tcs.OnlineMatchingPolicy

/-!
# optimal_online_matching_policy

Topic: online_algorithms   Node: 605d18ee7085

Provenance: formalization of a published result. Source: arXiv:2611.13571: Improved Bounds for Online Matching with Random Edge Arrivals, Lemma 5.1

For every simple graph G on vertex set Fin n with decidable adjacency, the optimal online matching policy achieves policy_value G (optimal_online_policy G) ∅ Finset.univ = bellman_value G ∅ Finset.univ, and every online matching policy pol : OnlineMatchingPolicy n satisfies policy_value G pol ∅ Finset.univ ≤ bellman_value G ∅ Finset.univ.
-/

/-- Optimal online matching policy on graphs known up to isomorphism (Lemma 5.1). -/
theorem optimal_online_matching_policy {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    policy_value G (optimal_online_policy G) ∅ Finset.univ = bellman_value G ∅ Finset.univ ∧
    ∀ (pol : OnlineMatchingPolicy n),
      policy_value G pol ∅ Finset.univ ≤ bellman_value G ∅ Finset.univ := by
  constructor
  · exact optimal_online_matching_policy_achieves_value G ∅ Finset.univ
  · intro pol
    exact online_matching_policy_value_le_bellman G pol ∅ Finset.univ
