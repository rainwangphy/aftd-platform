import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SetupFiniteGadgets
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample

/-!
# op2130_setup_replay_append

Topic: online_algorithms   Node: b06147d849fa

Provenance: helper lemma. OP-2130, appending an untouched discrepancy suffix

A local discrepancy schedule whose request endpoints lie inside a list leaves any appended suffix untouched.
-/

theorem op2130_append_aux_step (d s : List ℤ) (j : ℕ) (c : Bool)
    (h : j+1 < d.length) :
    op2130_mc_step (d ++ s) j c = op2130_mc_step d j c ++ s := by
  have h0 : (d ++ s).getD j 0 = d.getD j 0 := by
    exact List.getD_append d s 0 j (by omega)
  have h1 : (d ++ s).getD (j+1) 0 = d.getD (j+1) 0 := by
    exact List.getD_append d s 0 (j+1) h
  simp only [op2130_mc_step, h0, h1]
  rw [List.set_append_left _ _ (by omega)]
  rw [List.set_append_left _ _ (by simp; omega)]

theorem op2130_setup_replay_append (d s : List ℤ) (ops : List (ℕ × Bool)) (h : ∀ p ∈ ops, p.1 + 1 < d.length) : op2130_setup_replay (d ++ s) ops = op2130_setup_replay d ops ++ s := by
  unfold op2130_setup_replay
  induction ops generalizing d with
  | nil => rfl
  | cons q qs ih =>
      rcases q with ⟨j,c⟩
      simp only [List.foldl_cons]
      rw [op2130_append_aux_step d s j c (h (j,c) (by simp))]
      apply ih
      intro p hp
      have hh := h p (by simp [hp])
      simpa [op2130_mc_step] using hh
