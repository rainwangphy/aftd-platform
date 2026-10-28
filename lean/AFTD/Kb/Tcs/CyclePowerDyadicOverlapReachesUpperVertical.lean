import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSixteenBlockOverlapReachesUpperVertical
import AFTD.Kb.Tcs.CyclePowerDyadicSixteenBlockGeometry
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_overlap_reaches_upper_vertical

Topic: combinatorics   Node: 10338b85234a

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

In any tight dyadic rooted model of radius2^(k+4) with all-rank exactness, full ordinary coverage and monotone outer eighths, any overlap A_t,C_t selected and A_s missing for t<s<2^(k+1) forces an upper-half vertical defect at some root:2^k<=a<2^(k+1), C_a selected and A_a missing.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_overlap_reaches_upper_vertical
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
    (p : ℤ) (t s : ℕ) (hts : t < s) (hsq : s < 2^(k+1))
    (hA : x p t = true) (hC : x p (2^(k+1)+t) = true) (hm : x p s = false) :
    ∃ (r : ℤ) (a : ℕ), 2^k ≤ a ∧ a < 2^(k+1) ∧
      x r (2^(k+1)+a) = true ∧ x r a = false := by
  have M := cycle_power_dyadic_sixteen_block_geometry k x htight hexact hcover houter
  have h1 : 2^(k+1)=2*(2^k) := by rw [pow_succ]; omega
  have ans := cycle_power_sixteen_block_overlap_reaches_upper_vertical (2^k) x M p t s hts (by omega)
    hA (by simpa only [h1] using hC) hm
  simpa only [h1] using ans
