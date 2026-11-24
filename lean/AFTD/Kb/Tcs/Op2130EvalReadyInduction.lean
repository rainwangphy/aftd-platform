import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130CircuitAdvanceOrAnd
import AFTD.Kb.Tcs.Op2130CircuitAdvanceAndOr
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal

/-!
# op2130_eval_ready_induction

Topic: online_algorithms   Node: 1f8da4f3fb57

Provenance: helper lemma. OP-2130, induction for the prepared decision circuit

An arbitrary number of four-request circuit advances preserves the encoded gate value, all untouched bit and gate coordinates, and the AND compatibility invariant; the resulting Boolean is the corresponding alternating fold.
-/

set_option maxHeartbeats 1000000
def op2130_eval_next (i : ℕ) (a : Bool) (bits : ℕ → Bool) : Bool :=
  if (i+1) % 2 = 0 then a || bits (i+1) else a && bits (i+1)

def op2130_eval_advance (h : ℕ → ℤ) (i : ℕ) (coins : ℕ → Bool) : ℕ → ℤ :=
  let p := 2 + 2*i
  let h1 := op2130_height_double h (p+1) (coins (4*i)) (coins (4*i+1))
  op2130_height_double h1 (p+2) (coins (4*i+2)) (coins (4*i+3))

def op2130_eval_ready (N i : ℕ) (h : ℕ → ℤ) (bits : ℕ → Bool) (a : Bool) : Prop :=
  (if i % 2 = 0 then h (2+2*i) = (if a then 1 else -1)
    else h (2+2*i) = (if a then 2 else 0)) ∧
  (∀ j, i ≤ j → j < N → h (3+2*j) =
    if j % 2 = 0 then (if bits j then 2 else 0) else (if bits j then 1 else -1)) ∧
  (∀ j, i < j → j < N → h (2+2*j) = if j % 2 = 0 then -1 else 2) ∧
  (i % 2 = 1 → bits i = false → a = false)

theorem op2130_eval_ready_next (N i : ℕ) (h : ℕ → ℤ) (bits coins : ℕ → Bool) (a : Bool)
    (hi : i+1 < N) (hr : op2130_eval_ready N i h bits a) :
    op2130_eval_ready N (i+1) (op2130_eval_advance h i coins) bits (op2130_eval_next i a bits) := by
  rcases hr with ⟨hcur,hbits,hgates,hcorr⟩
  let p := 2+2*i
  let h1 := op2130_height_double h (p+1) (coins (4*i)) (coins (4*i+1))
  let h2 := op2130_height_double h1 (p+2) (coins (4*i+2)) (coins (4*i+3))
  have hsame : ∀ k, k ≠ p+1 → k ≠ p+2 → h2 k = h k := by
    intro k hk1 hk2
    dsimp only [h2,h1]
    rw [op2130_height_double_other _ _ _ _ _ hk2,
      op2130_height_double_other _ _ _ _ _ hk1]
  have parity : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hnew : if (i+1) % 2 = 0 then h2 (2+2*(i+1)) = (if op2130_eval_next i a bits then 1 else -1)
      else h2 (2+2*(i+1)) = (if op2130_eval_next i a bits then 2 else 0) := by
    rcases parity with he | ho
    · have hn : (i+1)%2 = 1 := by omega
      have ha : h p = if a then 1 else -1 := by simpa [p,he] using hcur
      have hx : h (p+1) = if bits i then 2 else 0 := by
        have hh := hbits i (by omega) (by omega)
        simpa [p,he,show 3+2*i = (2+2*i)+1 by omega] using hh
      have hg : h (p+2) = 2 := by
        have hh := hgates (i+1) (by omega) hi
        simpa [p,hn,show 2+2*(i+1)=(2+2*i)+2 by omega] using hh
      have hy : h (p+3) = if bits (i+1) then 1 else -1 := by
        have hh := hbits (i+1) (by omega) hi
        simpa [p,hn,show 3+2*(i+1)=(2+2*i)+3 by omega] using hh
      have hh := op2130_circuit_advance_or_and h p a (bits i) (bits (i+1))
        (coins (4*i)) (coins (4*i+1)) (coins (4*i+2)) (coins (4*i+3)) ha hx hg hy
      simpa [h2,h1,op2130_eval_next,hn,p,show 2+2*(i+1)=(2+2*i)+2 by omega] using hh
    · have hn : (i+1)%2 = 0 := by omega
      have ha : h p = if a then 2 else 0 := by simpa [p,show i%2≠0 by omega] using hcur
      have hx : h (p+1) = if bits i then 1 else -1 := by
        have hh := hbits i (by omega) (by omega)
        simpa [p,show i%2≠0 by omega,show 3+2*i = (2+2*i)+1 by omega] using hh
      have hg : h (p+2) = -1 := by
        have hh := hgates (i+1) (by omega) hi
        simpa [p,hn,show 2+2*(i+1)=(2+2*i)+2 by omega] using hh
      have hy : h (p+3) = if bits (i+1) then 2 else 0 := by
        have hh := hbits (i+1) (by omega) hi
        simpa [p,hn,show 3+2*(i+1)=(2+2*i)+3 by omega] using hh
      have hh := op2130_circuit_advance_and_or h p a (bits i) (bits (i+1))
        (coins (4*i)) (coins (4*i+1)) (coins (4*i+2)) (coins (4*i+3)) ha hx (hcorr ho) hg hy
      simpa [h2,h1,op2130_eval_next,hn,p,show 2+2*(i+1)=(2+2*i)+2 by omega] using hh
  change op2130_eval_ready N (i+1) h2 bits (op2130_eval_next i a bits)
  refine ⟨hnew, ?_, ?_, ?_⟩
  · intro j hj hjN
    rw [hsame (3+2*j) (by dsimp [p]; omega) (by dsimp [p]; omega)]
    exact hbits j (by omega) hjN
  · intro j hj hjN
    rw [hsame (2+2*j) (by dsimp [p]; omega) (by dsimp [p]; omega)]
    exact hgates j (by omega) hjN
  · intro hp hb
    simp [op2130_eval_next, show (i+1)%2 ≠ 0 by omega, hb]

def op2130_eval_steps (coins : ℕ → Bool) : ℕ → ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, _, h => h
  | m+1, i, h => op2130_eval_steps coins m (i+1) (op2130_eval_advance h i coins)

def op2130_eval_acc (bits : ℕ → Bool) : ℕ → ℕ → Bool → Bool
  | 0, _, a => a
  | m+1, i, a => op2130_eval_acc bits m (i+1) (op2130_eval_next i a bits)

theorem op2130_eval_ready_induction (N m i : ℕ) (h : ℕ → ℤ) (bits coins : ℕ → Bool) (a : Bool)
    (hi : i+m < N) (hr : op2130_eval_ready N i h bits a) :
    op2130_eval_ready N (i+m) (op2130_eval_steps coins m i h) bits (op2130_eval_acc bits m i a) := by
  induction m generalizing i h a with
  | zero => simpa [op2130_eval_steps,op2130_eval_acc] using hr
  | succ m ih =>
      have h1 := op2130_eval_ready_next N i h bits coins a (by omega) hr
      have hh := ih (i+1) (op2130_eval_advance h i coins) (op2130_eval_next i a bits) (by omega) h1
      simpa only [op2130_eval_steps,op2130_eval_acc,show i+(m+1) = (i+1)+m by omega] using hh
