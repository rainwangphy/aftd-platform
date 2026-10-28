import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockChildForcesFullPrefix
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_sixteen_block_second_eighth_monotone

Topic: combinatorics   Node: 0e8938f8e10f

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Under the Geometry hypotheses and the global no-vertical condition C_t implies A_t, the second eighth is an initial segment: u<=t<2h and C_t selected imply C_u selected.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_sixteen_block_second_eighth_monotone
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (p : ℤ) (u t : ℕ) (hut : u ≤ t) (ht : t < 2*h)
    (hC : x p (2*h+t) = true) : x p (2*h+u) = true := by
  by_cases he : u=t
  · simpa only [he] using hC
  have hut' : u < t := by omega
  let L := t-u
  have hL : 0 < L := by dsimp [L]; omega
  have hLq : L < 2*h := by dsimp [L]; omega
  let v : ℤ := p+(2*h : ℕ)+(u : ℤ)
  obtain ⟨a,ha,hA,hB⟩ := M.cover (12*h+L) (by have := M.pos; omega) (by omega) v
  let r : ℤ := v-(a : ℤ)
  have ha4 : a < 4*h-L := by omega
  have hAt := nov p t ht hC
  have hZt := M.childZ p t ht hC
  by_cases ha0 : a+L < 2*h
  · have hl : x r (a+L) = true := by
      apply (M.parent6 r (a+L) (by omega)).1 ha0
      convert hB using 1 <;> congr 1 <;> omega
    have heq := M.own6 r p (a+L) (2*h+t) (by omega) (by omega)
      (by dsimp [r,v,L]; omega) hl
      (by convert hB using 1 <;> congr 1 <;> omega) hC
      (by convert hZt using 1 <;> congr 1 <;> omega)
    dsimp [r,v,L] at heq
    omega
  · by_cases haq : a < 2*h
    · let b := a+L-2*h
      have hb : b < 2*h := by dsimp [b]; omega
      have hba : b ≤ a := by dsimp [b]; omega
      have hl : x r b = true := M.lowMono r b a hba haq hA
      have hz : x r (b+14*h) = true := by convert hB using 1 <;> congr 1 <;> dsimp [b] <;> omega
      have heq := M.own7 r p b t hb ht (by dsimp [r,v,b,L]; omega) hl hz hAt
        (by convert hZt using 1 <;> congr 1 <;> omega)
      dsimp [r,v,L] at heq
      omega
    · let b := a-2*h
      have hb : b < 2*h := by dsimp [b]; omega
      have hbL : b+L < 2*h := by dsimp [b]; omega
      have hc : x r (2*h+b) = true := by convert hA using 1 <;> congr 1 <;> dsimp [b] <;> omega
      have hfull := cycle_power_sixteen_block_child_forces_full_prefix h x M nov r b hb hc
      have hz : x r (b+L+14*h) = true := by convert hB using 1 <;> congr 1 <;> dsimp [b] <;> omega
      have heq := M.own7 r p (b+L) t hbL ht (by dsimp [r,v,b,L]; omega) (hfull (b+L) hbL) hz hAt
        (by convert hZt using 1 <;> congr 1 <;> omega)
      dsimp [r,v] at heq
      convert hA using 1 <;> congr 1 <;> omega
