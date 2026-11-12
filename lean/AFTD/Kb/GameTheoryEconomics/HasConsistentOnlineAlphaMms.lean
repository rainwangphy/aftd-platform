import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConsistentOnlineAllocator
import AFTD.Kb.GameTheoryEconomics.IsPrefixAlphaMmsChores

/-!
# has_consistent_online_alpha_mms

Topic: fair_division   Node: 362fe7d5e271

Provenance: original. Related work: arXiv:2505.24321

Given ratio r and approximation factor α, there exists a consistent online allocator for two agents that, whenever each agent's cost for each chore is in {1, r} (not necessarily identical between the two agents), guarantees an α-MMS allocation after every prefix of every length.
-/

/-- Given ratio r and factor alpha, there exists a consistent online allocator guaranteeing alpha-MMS after every prefix for two agents with chore costs in {1, r}. -/
def has_consistent_online_alpha_mms (r α : ℝ) : Prop :=
  ∃ alg, is_consistent_online_allocator alg ∧
    ∀ (m : ℕ) (c : Fin 2 → Fin m → ℝ),
      (∀ i g, c i g = 1 ∨ c i g = r) →
      is_prefix_alpha_mms_chores m α c (alg m c)
