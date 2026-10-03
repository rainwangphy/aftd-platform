import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvCheck

/-!
# lxv_check_eq_true

Topic: fair_division   Node: 6d0b867070fb

The finite check lxv_check evaluates to true (kernel computation).
-/

lemma lxv_check_eq_true : lxv_check = true := by decide +kernel
