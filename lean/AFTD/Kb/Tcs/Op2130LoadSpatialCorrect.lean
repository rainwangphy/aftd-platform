import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130HeightDoubleLocal
import AFTD.Kb.Tcs.Op2130LoadBitGadgets
import AFTD.Kb.Tcs.Op2130HeightStep
import AFTD.Kb.Tcs.Op2130DecisionGates

/-!
# op2130_load_spatial_correct

Topic: online_algorithms   Node: 9f839650350e

Provenance: helper lemma. OP-2130, localized decision-circuit bit preparation

The even and odd bit-loading gadgets set exactly the desired local Boolean signal and gate value while leaving every other height unchanged, regardless of dummy coins.
-/

set_option maxHeartbeats 1000000

def op2130_run_at (j : ℕ) : List Bool → (ℕ → ℤ) → ℕ → ℤ
  | [], h => h
  | c::cs, h => op2130_run_at j cs (op2130_height_step h j c)

def op2130_run_scalar (l r : ℤ) : List Bool → ℤ → ℤ
  | [], m => m
  | c::cs, m => op2130_run_scalar l r cs (op2130_gate_update l m r c)

theorem op2130_run_at_other (j k : ℕ) (cs : List Bool) (h : ℕ → ℤ) (hne : k ≠ j) :
    op2130_run_at j cs h k = h k := by
  induction cs generalizing h with
  | nil => rfl
  | cons c cs ih =>
      rw [op2130_run_at, ih]
      simp only [op2130_height_step, Function.update_of_ne hne]

theorem op2130_run_at_center (j : ℕ) (hj : 1 ≤ j) (cs : List Bool) (h : ℕ → ℤ) :
    op2130_run_at j cs h j = op2130_run_scalar (h (j-1)) (h (j+1)) cs (h j) := by
  induction cs generalizing h with
  | nil => rfl
  | cons c cs ih =>
      rw [op2130_run_at, ih]
      have hleft : j-1 ≠ j := by omega
      have hright : j+1 ≠ j := by omega
      simp only [op2130_height_step, Function.update_of_ne hleft,
        Function.update_of_ne hright, Function.update_self, op2130_run_scalar,
        op2130_gate_update]

def op2130_load_even_spatial (h : ℕ → ℤ) (p : ℕ) (c d1 d2 d3 d4 d5 : Bool) : ℕ → ℤ :=
  let h1 := op2130_run_at (p+1) [d1,d2,d3,d4,c] h
  op2130_height_step h1 p d5

theorem op2130_load_even_spatial_correct (h : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (c d1 d2 d3 d4 d5 : Bool) (hl : h (p-1) = -3) (hg : h p = 0)
    (hb : h (p+1) = 5) (hr : h (p+2) = 2) :
    let out := op2130_load_even_spatial h p c d1 d2 d3 d4 d5
    out p = -1 ∧ out (p+1) = (if c then 2 else 0) ∧
      ∀ k, k ≠ p → k ≠ p+1 → out k = h k := by
  let h1 := op2130_run_at (p+1) [d1,d2,d3,d4,c] h
  have hc := op2130_run_at_center (p+1) (by omega) [d1,d2,d3,d4,c] h
  simp only [show p+1-1=p by omega,show p+1+1=p+2 by omega, hg,hr,hb,
    op2130_run_scalar] at hc
  have scalar := op2130_load_even_bit c d1 d2 d3 d4 d5
  dsimp only at scalar
  have hbit : h1 (p+1) = if c then 2 else 0 := by
    change op2130_run_at (p+1) [d1,d2,d3,d4,c] h (p+1) = _
    rw [hc, scalar.2.1]
  have hp1 : h1 p = 0 := by
    dsimp only [h1]
    rw [op2130_run_at_other _ _ _ _ (by omega),hg]
  have hl1 : h1 (p-1) = -3 := by
    dsimp only [h1]
    rw [op2130_run_at_other _ _ _ _ (by omega),hl]
  have hgate : op2130_height_step h1 p d5 p = -1 := by
    simp only [op2130_height_step, Function.update_self,hl1,hp1,hbit]
    simpa [op2130_gate_update] using scalar.2.2
  change op2130_height_step h1 p d5 p = -1 ∧
    op2130_height_step h1 p d5 (p+1) = (if c then 2 else 0) ∧
      ∀ k, k ≠ p → k ≠ p+1 → op2130_height_step h1 p d5 k = h k
  refine ⟨hgate, ?_, ?_⟩
  · simp only [op2130_height_step,Function.update_of_ne (show p+1 ≠ p by omega),hbit]
  · intro k hkp hkb
    simp only [op2130_height_step,Function.update_of_ne hkp]
    exact op2130_run_at_other _ _ _ _ hkb

def op2130_load_odd_spatial (h : ℕ → ℤ) (p : ℕ) (c d1 d2 d3 d4 : Bool) : ℕ → ℤ :=
  let h1 := op2130_run_at (p+1) [d1,d2,d3,c] h
  op2130_height_step h1 p d4

theorem op2130_load_odd_spatial_correct (h : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (c d1 d2 d3 d4 : Bool) (hl : h (p-1) = 5) (hg : h p = 1)
    (hb : h (p+1) = -3) (hr : h (p+2) = -1) :
    let out := op2130_load_odd_spatial h p c d1 d2 d3 d4
    out p = 2 ∧ out (p+1) = (if c then 1 else -1) ∧
      ∀ k, k ≠ p → k ≠ p+1 → out k = h k := by
  let h1 := op2130_run_at (p+1) [d1,d2,d3,c] h
  have hc := op2130_run_at_center (p+1) (by omega) [d1,d2,d3,c] h
  simp only [show p+1-1=p by omega,show p+1+1=p+2 by omega, hg,hr,hb,
    op2130_run_scalar] at hc
  have scalar := op2130_load_odd_bit c d1 d2 d3 d4
  dsimp only at scalar
  have hbit : h1 (p+1) = if c then 1 else -1 := by
    change op2130_run_at (p+1) [d1,d2,d3,c] h (p+1) = _
    rw [hc, scalar.2.1]
  have hp1 : h1 p = 1 := by
    dsimp only [h1]
    rw [op2130_run_at_other _ _ _ _ (by omega),hg]
  have hl1 : h1 (p-1) = 5 := by
    dsimp only [h1]
    rw [op2130_run_at_other _ _ _ _ (by omega),hl]
  have hgate : op2130_height_step h1 p d4 p = 2 := by
    simp only [op2130_height_step, Function.update_self,hl1,hp1,hbit]
    simpa [op2130_gate_update] using scalar.2.2
  change op2130_height_step h1 p d4 p = 2 ∧
    op2130_height_step h1 p d4 (p+1) = (if c then 1 else -1) ∧
      ∀ k, k ≠ p → k ≠ p+1 → op2130_height_step h1 p d4 k = h k
  refine ⟨hgate, ?_, ?_⟩
  · simp only [op2130_height_step,Function.update_of_ne (show p+1 ≠ p by omega),hbit]
  · intro k hkp hkb
    simp only [op2130_height_step,Function.update_of_ne hkp]
    exact op2130_run_at_other _ _ _ _ hkb

theorem op2130_load_spatial_correct :
    (∀ (h : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p) (c d1 d2 d3 d4 d5 : Bool),
      h (p-1) = -3 → h p = 0 → h (p+1) = 5 → h (p+2) = 2 →
      let out := op2130_load_even_spatial h p c d1 d2 d3 d4 d5
      out p = -1 ∧ out (p+1) = (if c then 2 else 0) ∧
        ∀ k, k ≠ p → k ≠ p+1 → out k = h k) ∧
    (∀ (h : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p) (c d1 d2 d3 d4 : Bool),
      h (p-1) = 5 → h p = 1 → h (p+1) = -3 → h (p+2) = -1 →
      let out := op2130_load_odd_spatial h p c d1 d2 d3 d4
      out p = 2 ∧ out (p+1) = (if c then 1 else -1) ∧
        ∀ k, k ≠ p → k ≠ p+1 → out k = h k) := by
  exact ⟨fun h p hp c d1 d2 d3 d4 d5 hl hg hb hr =>
      op2130_load_even_spatial_correct h p hp c d1 d2 d3 d4 d5 hl hg hb hr,
    fun h p hp c d1 d2 d3 d4 hl hg hb hr =>
      op2130_load_odd_spatial_correct h p hp c d1 d2 d3 d4 hl hg hb hr⟩
