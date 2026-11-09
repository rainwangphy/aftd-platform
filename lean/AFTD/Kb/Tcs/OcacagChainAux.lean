import AFTD.Prelude
import AFTD.Kb.Tcs.OcacagSplit

/-!
# ocacagChainAux

Topic: online_algorithms   Node: 2f1d64c7ea63

Provenance: helper lemma. step towards online_cycle_augmentation_adversary_cost_ge

The list of nested dyadic cuts obtained by starting at interval c and bisecting t times toward the vertex v: [c] for t = 0, and c :: ocacagChainAux t (ocacagSplit c v) v for t = t'+1.
-/

/-- The chain of nested dyadic cuts from `c` towards the vertex `v`. -/
def ocacagChainAux : ℕ → ℤ × ℤ → ℤ → List (ℤ × ℤ) := fun t c v =>
  match t with
  | 0 => [c]
  | (t + 1) => c :: ocacagChainAux t (ocacagSplit c v) v
