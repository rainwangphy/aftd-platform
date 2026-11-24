import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.Tcs.Op2130PathPrefixDiscrepanciesCoinMonotone
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op2130_path_height_step_bridge

Topic: online_algorithms   Node: d292d4c13f72

Provenance: helper lemma. OP-2130, correspondence of path heights and greedy discrepancies

For a left-to-right path request, the cumulative discrepancy profile after the greedy update is exactly the local height update at the crossing index.
-/

theorem op2130_path_height_step_bridge {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (he : e.2.val = e.1.val + 1) (c : Bool) (k : ℕ) : op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) k = op2130_height_step (op_2130_path_prefix_discrepancies_coin_monotone_pfx d) (e.1.val + 1) c k := by
  by_cases hk : k = e.1.val + 1
  · subst k
    rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid d e _ he,
      op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_inc d e c he]
    simp only [op2130_height_step, Function.update_self, Nat.add_sub_cancel,
      show e.1.val + 1 + 1 = e.1.val + 2 by omega]
  · have hne : k ≠ e.1.val+1 := hk
    by_cases hlo : k ≤ e.1.val
    · rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low d e _ k he hlo]
      simp only [op2130_height_step, Function.update_of_ne hne]
    · have hhi : e.1.val+2 ≤ k := by omega
      rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high d e _ k he hhi]
      simp only [op2130_height_step, Function.update_of_ne hne]
