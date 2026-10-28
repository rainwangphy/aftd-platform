import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockVerticalDefectUpperHalf
import AFTD.Kb.Tcs.CyclePowerSixteenBlockLeftQuarterOfNoVertical
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_sixteen_block_left_defect_reaches_upper_vertical

Topic: combinatorics   Node: d4ec1113fd57

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Under the Geometry hypotheses, every first-quarter prefix defect (a<=b<4h, position a missing and b selected) forces an upper-half vertical defect at some integer root.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_sixteen_block_left_defect_reaches_upper_vertical
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (p : ℤ) (a b : ℕ) (hab : a ≤ b) (hb : b < 4*h)
    (hm : x p a = false) (hs : x p b = true) :
    ∃ (r : ℤ) (t : ℕ), h ≤ t ∧ t < 2*h ∧ x r (2*h+t) = true ∧ x r t = false := by
  by_contra hn
  have nov : ∀ r a, a < 2*h → x r (2*h+a) = true → x r a = true := by
    intro r a ha hc
    by_contra hne
    have hm : x r a = false := Bool.eq_false_iff.mpr hne
    have hah := cycle_power_eight_block_vertical_defect_upper_half h x M.parent6 M.parent7 r a ha hc hm
    exact hn ⟨r,a,hah,ha,hc,hm⟩
  have hh := cycle_power_sixteen_block_left_quarter_of_no_vertical h x M nov p a b hab hb hs
  rw [hm] at hh
  contradiction
