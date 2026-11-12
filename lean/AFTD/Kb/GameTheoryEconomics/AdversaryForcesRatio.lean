import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPrefixAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.IsOnlineAllocator

/-!
# adversary_forces_ratio

Topic: fair_division   Node: dea2c45cb145

Provenance: original. Related work: arXiv:2505.24321

Given ratio r, factor α, and horizon H, an adversary forces factor α by prefix H on two agents if for every online allocator on H chores, there exists a cost profile assigning values in {1, r} to each agent and chore (not necessarily identical between the two agents) such that the resulting allocation fails to be α-MMS after every prefix.
-/

/-- An adversary forces factor alpha by horizon H if every online allocator on H chores fails to maintain alpha-MMS after every prefix on some instance with costs in {1, r}. -/
def adversary_forces_ratio (r α : ℝ) (H : ℕ) : Prop :=
  ∀ alg, is_online_allocator 2 H alg →
    ∃ c : Fin 2 → Fin H → ℝ, (∀ i g, c i g = 1 ∨ c i g = r) ∧
      ¬ is_prefix_alpha_mms_chores H α c (alg c)
