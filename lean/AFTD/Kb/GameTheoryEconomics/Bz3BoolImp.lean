import AFTD.Prelude

/-!
# bz3_bool_imp

Topic: general_equilibrium   Node: ab130fd564e1

For Booleans, (not a or b) is true iff a true implies b true.
-/

lemma bz3_bool_imp (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp
