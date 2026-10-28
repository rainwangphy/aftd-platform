import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockNoVerticalOverlap

/-!
# cycle_power_sixteen_block_child_forces_full_prefix

Topic: combinatorics   Node: f4adcfaa03cb

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

Under the explicit Geometry hypotheses and the global no-vertical-defect condition C_t implies A_t, every root with any selected C_t has its entire first2h prefix selected.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_sixteen_block_child_forces_full_prefix
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (p : ℤ) (t : ℕ) (ht : t < 2*h) (hC : x p (2*h+t) = true) :
    ∀ s < 2*h, x p s = true := by
  intro s hs
  by_contra hn
  have hmiss : x p s = false := Bool.eq_false_iff.mpr hn
  have hA := nov p t ht hC
  by_cases hst : s ≤ t
  · have ha := M.lowMono p s t hst ht hA
    rw [hmiss] at ha
    contradiction
  · exact cycle_power_sixteen_block_no_vertical_overlap h x M nov p t s (by omega) hs hA hC hmiss
