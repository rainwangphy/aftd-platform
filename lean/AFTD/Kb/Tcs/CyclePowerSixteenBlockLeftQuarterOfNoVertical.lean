import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockChildForcesFullPrefix
import AFTD.Kb.Tcs.CyclePowerSixteenBlockSecondEighthMonotone
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_sixteen_block_left_quarter_of_no_vertical

Topic: combinatorics   Node: 3350cfd9b387

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Under the Geometry hypotheses and the global no-vertical condition C_t implies A_t, every first quarter of length4h is a selected initial segment. No right-quarter or count-preservation conclusion is asserted.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_sixteen_block_left_quarter_of_no_vertical
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true) :
    ∀ (p : ℤ) (a b : ℕ), a ≤ b → b < 4*h → x p b = true → x p a = true := by
  intro p a b hab hb hx
  by_cases hbq : b < 2*h
  · exact M.lowMono p a b hab hbq hx
  · let t := b-2*h
    have ht : t < 2*h := by dsimp [t]; omega
    have hc : x p (2*h+t) = true := by convert hx using 1 <;> congr 1 <;> dsimp [t] <;> omega
    by_cases haq : a < 2*h
    · exact cycle_power_sixteen_block_child_forces_full_prefix h x M nov p t ht hc a haq
    · have hu : a-2*h ≤ t := by dsimp [t]; omega
      have hh := cycle_power_sixteen_block_second_eighth_monotone h x M nov p (a-2*h) t hu ht hc
      convert hh using 1 <;> congr 1 <;> omega
