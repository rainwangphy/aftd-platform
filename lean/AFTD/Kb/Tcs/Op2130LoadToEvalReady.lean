import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130LoadProfileCorrect
import AFTD.Kb.Tcs.Op2130EvalReadyInduction
import AFTD.Kb.Tcs.Op2130LoadBitGadgets
import AFTD.Kb.Tcs.Op2130DecisionGates
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal

/-!
# op2130_load_to_eval_ready

Topic: online_algorithms   Node: cfb3e7f6a9f2

Provenance: helper lemma. OP-2130, prepared decision circuit

After the reverse loading invariant holds, four fixed local updates establish the initial invariant for the verified left-to-right gate evaluator, independent of their dummy coins.
-/

theorem op2130_load_to_eval_ready (N : ℕ) (h : ℕ → ℤ) (bits : ℕ → Bool)
    (c1 c2 c3 c4 : Bool) (hN : 0 < N) (hinv : op2130_load_inv N 0 h bits) :
    let h1 := op2130_height_double h 1 c1 c2
    let h2 := op2130_height_double h1 2 c3 c4
    op2130_eval_ready N 0 h2 bits (bits 0) := by
  rcases hinv with ⟨hz,href,hsentinel,hgate0,hbit0,hgate1,hbit1⟩
  have hg0 : h 2 = -1 := by simpa using hgate1 0 (by omega) hN
  have hb0 : h 3 = if bits 0 then 2 else 0 := by simpa using hbit1 0 (by omega) hN
  let h1 := op2130_height_double h 1 c1 c2
  let h2 := op2130_height_double h1 2 c3 c4
  have h1one : h1 1 = -1 := by
    have hh := op2130_height_double_center h 1 (by omega) c1 c2
    simp only [show (1:ℕ)-1=0 by omega,show (1:ℕ)+1=2 by omega,hz,href,hg0] at hh
    change h1 1 = _ at hh
    rw [hh]
    exact op2130_load_left_reference c1 c2
  have h1two : h1 2 = -1 := by
    dsimp only [h1]
    rw [op2130_height_double_other _ _ _ _ _ (by omega),hg0]
  have h1three : h1 3 = if bits 0 then 2 else 0 := by
    dsimp only [h1]
    rw [op2130_height_double_other _ _ _ _ _ (by omega),hb0]
  have h2two : h2 2 = if bits 0 then 1 else -1 := by
    have hh := op2130_height_double_center h1 2 (by omega) c3 c4
    simp only [show (2:ℕ)-1=1 by omega,show (2:ℕ)+1=3 by omega,h1one,h1two,h1three] at hh
    change h2 2 = _ at hh
    rw [hh]
    have hx : (if bits 0 then (2:ℤ) else 0) = 0 ∨ (if bits 0 then (2:ℤ) else 0) = 2 := by
      cases bits 0 <;> simp
    have ho := op2130_decision_or (if bits 0 then (2:ℤ) else 0) (-1) c3 c4 hx (by simp)
    cases hb : bits 0 <;> simpa [hb] using ho
  have hsame : ∀ k, k ≠ 1 → k ≠ 2 → h2 k = h k := by
    intro k hk1 hk2
    dsimp only [h2,h1]
    rw [op2130_height_double_other _ _ _ _ _ hk2,
      op2130_height_double_other _ _ _ _ _ hk1]
  change op2130_eval_ready N 0 h2 bits (bits 0)
  refine ⟨?_,?_,?_,?_⟩
  · simpa using h2two
  · intro j hj hjN
    rw [hsame (3+2*j) (by omega) (by omega)]
    exact hbit1 j (by omega) hjN
  · intro j hj hjN
    rw [hsame (2+2*j) (by omega) (by omega)]
    exact hgate1 j (by omega) hjN
  · intro hp
    omega
