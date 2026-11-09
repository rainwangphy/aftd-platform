import AFTD.Prelude
import AFTD.Kb.Tcs.OcacagChainAux
import AFTD.Kb.Tcs.OcacagSplit

/-!
# ocacagChain

Topic: online_algorithms   Node: 86614de143ab

Provenance: helper lemma. step towards online_cycle_augmentation_adversary_cost_ge

The dyadic chain to leaf v: start at the top cut [1, 2^(k-1)] and bisect k-1 times toward v, giving k nested cuts down to the singleton {v}.
-/

/-- The dyadic chain of cuts leading to the vertex `v`, starting from the top cut [1, 2^(k-1)]. -/
def ocacagChain (k : ℕ) (v : ℤ) : List (ℤ × ℤ) := ocacagChainAux (k - 1) (1, (2 : ℤ) ^ (k - 1)) v
