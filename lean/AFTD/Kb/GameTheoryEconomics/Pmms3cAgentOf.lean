import AFTD.Prelude

/-!
# pmms3c_agent_of

Topic: fair_division   Node: 3836a2050867

The agent w mod 3.
-/

/-- `w mod 3` as an agent. -/
def pmms3c_agent_of (w : ℕ) : Fin 3 := ⟨w % 3, Nat.mod_lt _ (by norm_num)⟩
