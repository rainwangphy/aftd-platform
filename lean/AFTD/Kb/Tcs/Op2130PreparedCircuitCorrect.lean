import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130LoadProfileCorrect
import AFTD.Kb.Tcs.Op2130LoadToEvalReady
import AFTD.Kb.Tcs.Op2130EvalReadyInduction
import AFTD.Kb.Tcs.Op2130EvalMatchesDecisionFold
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal

/-!
# op2130_prepared_circuit_correct

Topic: online_algorithms   Node: b8b9c03d93d2

Provenance: helper lemma. OP-2130, all-size prepared-profile decision circuit

For any number of alternating gates and any bit and dummy tapes, the prepared profile and reverse loading followed by left-to-right evaluation yield the precise last-vertex discrepancy as an alternating Boolean decision fold.
-/

theorem op2130_prepared_circuit_correct (m : ℕ) (bits loadCoins evalCoins : ℕ → Bool)
    (c1 c2 c3 c4 : Bool) :
    let h0 := op2130_load_reverse bits loadCoins (m+1) (op2130_load_profile (m+1))
    let h1 := op2130_height_double h0 1 c1 c2
    let h2 := op2130_height_double h1 2 c3 c4
    let out := op2130_eval_steps evalCoins m 0 h2
    let v := 2+2*m
    out (v+1) - out v =
      if m%2=0 then
        (if bits m then 2 else 0) - (if op2130_value_fold (m+1) bits then 1 else -1)
      else (if bits m then 1 else -1) - (if op2130_value_fold (m+1) bits then 2 else 0) := by
  let h0 := op2130_load_reverse bits loadCoins (m+1) (op2130_load_profile (m+1))
  let h1 := op2130_height_double h0 1 c1 c2
  let h2 := op2130_height_double h1 2 c3 c4
  let out := op2130_eval_steps evalCoins m 0 h2
  have hload : op2130_load_inv (m+1) 0 h0 bits := op2130_load_profile_correct (m+1) bits loadCoins
  have hstart : op2130_eval_ready (m+1) 0 h2 bits (bits 0) :=
    op2130_load_to_eval_ready (m+1) h0 bits c1 c2 c3 c4 (by omega) hload
  have hfinish := op2130_eval_ready_induction (m+1) m 0 h2 bits evalCoins (bits 0) (by omega) hstart
  have hg := hfinish.1
  have hb := hfinish.2.1 m (by omega) (by omega)
  simp only [Nat.zero_add, op2130_eval_matches_decision_fold] at hg
  change out (2+2*m+1) - out (2+2*m) = _
  dsimp only [out]
  by_cases he : m%2=0
  · simp only [he, if_true] at hg hb ⊢
    rw [show 2+2*m+1 = 3+2*m by omega, hb, hg]
  · simp only [he, if_false] at hg hb ⊢
    rw [show 2+2*m+1 = 3+2*m by omega, hb, hg]
