import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SetupFiniteGadgets
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample

/-!
# op2130_setup_replay_shift

Topic: online_algorithms   Node: 177b432f7382

Provenance: helper lemma. OP-2130, shifting a local greedy discrepancy schedule

A fixed local discrepancy schedule acts identically on a suffix when all its edge indices are shifted by the length of an untouched prefix.
-/

theorem op2130_shift_aux_step (p s : List ℤ) (j : ℕ) (c : Bool) :
    op2130_mc_step (p ++ s) (p.length+j) c = p ++ op2130_mc_step s j c := by
  have h0 : (p ++ s).getD (p.length+j) 0 = s.getD j 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have h1 : (p ++ s).getD (p.length+j+1) 0 = s.getD (j+1) 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hidx : p.length+j+1-p.length = j+1 := by omega
    rw [hidx]
  simp only [op2130_mc_step, h0, h1]
  simp [List.set_append_right, Nat.add_assoc]

theorem op2130_setup_replay_shift (p s : List ℤ) (ops : List (ℕ × Bool)) : op2130_setup_replay (p ++ s) (ops.map fun (j,c) => (p.length+j,c)) = p ++ op2130_setup_replay s ops := by
  unfold op2130_setup_replay
  induction ops generalizing s with
  | nil => rfl
  | cons q qs ih =>
      rcases q with ⟨j,c⟩
      simp only [List.map_cons, List.foldl_cons, op2130_shift_aux_step, ih]
