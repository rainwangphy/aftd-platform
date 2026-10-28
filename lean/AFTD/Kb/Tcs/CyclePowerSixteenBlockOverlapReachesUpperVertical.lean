import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockVerticalDefectUpperHalf
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_sixteen_block_overlap_reaches_upper_vertical

Topic: combinatorics   Node: d203f8d007b8

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Under the explicit Geometry hypotheses, every overlap A_t,C_t selected and A_s missing with t<s<2h forces some upper-half vertical defect: at another integer root r some h<=a<2h selects C_a but misses A_a.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_sixteen_block_overlap_reaches_upper_vertical
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (p : ℤ) (t s : ℕ) (hts : t < s) (hsq : s < 2*h)
    (hA : x p t = true) (hC : x p (2*h+t) = true) (hm : x p s = false) :
    ∃ (r : ℤ) (a : ℕ), h ≤ a ∧ a < 2*h ∧ x r (2*h+a) = true ∧ x r a = false := by
  by_contra hn
  have nov : ∀ r a, a < 2*h → x r (2*h+a) = true → x r a = true := by
    intro r a ha hc
    by_contra hne
    have hm : x r a = false := Bool.eq_false_iff.mpr hne
    have hah := cycle_power_eight_block_vertical_defect_upper_half h x M.parent6 M.parent7 r a ha hc hm
    exact hn ⟨r,a,hah,ha,hc,hm⟩
  exact cycle_power_sixteen_block_no_vertical_overlap h x M nov p t s hts hsq hA hC hm
