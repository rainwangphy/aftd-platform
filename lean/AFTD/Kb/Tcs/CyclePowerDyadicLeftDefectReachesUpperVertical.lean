import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicSixteenBlockGeometry
import AFTD.Kb.Tcs.CyclePowerSixteenBlockLeftDefectReachesUpperVertical
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_left_defect_reaches_upper_vertical

Topic: combinatorics   Node: bf96334759f9

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

In any tight dyadic rooted model of radius2^(k+4) with all-rank exactness, full ordinary coverage and monotone outer eighths, every first-quarter prefix defect a<=b<2^(k+2) forces some upper-half vertical defect: at a root r some2^k<=t<2^(k+1) has offset2^(k+1)+t selected but t missing. This is a structural reduction; it does not exclude that defect or settle OP-205.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_left_defect_reaches_upper_vertical
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+4) (x p) =
      (range (2^(k+4))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+4, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+4)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+4) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+4)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(k+1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 7*2^(k+1) ≤ a → a ≤ b → b < 2^(k+4) → x p a = true → x p b = true))
    (p : ℤ) (a b : ℕ) (hab : a ≤ b) (hb : b < 2^(k+2))
    (hm : x p a = false) (hs : x p b = true) :
    ∃ (r : ℤ) (t : ℕ), 2^k ≤ t ∧ t < 2^(k+1) ∧ x r (2^(k+1)+t) = true ∧ x r t = false := by
  have M := cycle_power_dyadic_sixteen_block_geometry k x htight hexact hcover houter
  have h1 : 2^(k+1)=2*(2^k) := by rw [pow_succ]; omega
  have h2 : 2^(k+2)=4*(2^k) := by rw [show k+2=(k+1)+1 by omega,pow_succ,h1]; omega
  have ans := cycle_power_sixteen_block_left_defect_reaches_upper_vertical (2^k) x M p a b hab
    (by omega) hm hs
  simpa only [h1] using ans
