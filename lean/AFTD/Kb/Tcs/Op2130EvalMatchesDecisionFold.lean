import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130EvalReadyInduction

/-!
# op2130_eval_matches_decision_fold

Topic: online_algorithms   Node: a03d7b3698a9

Provenance: helper lemma. OP-2130, decision-circuit evaluation

The recursive accumulator used by the verified gate-evaluation invariant equals the alternating OR/AND fold in the decision-circuit statement.
-/

def op2130_value_fold (N : ℕ) (bits : ℕ → Bool) : Bool :=
  (List.range N).foldl (fun a i => if i%2=0 then a || bits i else a && bits i) false

theorem op2130_eval_acc_fold (m i : ℕ) (bits : ℕ → Bool) (a : Bool) :
    op2130_eval_acc bits m i a = (List.range' (i+1) m).foldl
      (fun a j => if j%2=0 then a || bits j else a && bits j) a := by
  induction m generalizing i a with
  | zero => rfl
  | succ m ih =>
      simp only [op2130_eval_acc, List.range'_succ, List.foldl_cons]
      simpa only [op2130_eval_next] using ih (i+1) (op2130_eval_next i a bits)

theorem op2130_eval_matches_decision_fold (m : ℕ) (bits : ℕ → Bool) :
    op2130_eval_acc bits m 0 (bits 0) = op2130_value_fold (m+1) bits := by
  rw [op2130_eval_acc_fold]
  simp [op2130_value_fold, List.range_eq_range', List.range'_succ]
