import AFTD.Prelude

/-!
# op309_k23_network_charge_arithmetic

Topic: graphs   Node: 88898807ee33

Provenance: helper lemma. OP-309 bridgeless network counting.

Injective uncovered-to-supported charging and a per-block budget imply the network upper bound.
-/

theorem op309_k23_network_charge_arithmetic (u supported blocks : ℕ)
  (hcharge : u ≤ supported) (hlocal : u + supported ≤ 3 * blocks) :
  2 * u ≤ 3 * blocks := by omega
